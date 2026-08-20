#!/usr/bin/env python3
"""
Classify assertions and assumptions in CBMC proof directories.

Two complementary axes (see exploration/assertion_assumption_classification.md):

  A. Source-level: scan the proof's C files and classify each
     assume/assert primitive by construct, file role (harness/stub/source)
     and a heuristic intent.

  B. Result-level: parse viewer-result.json or build/reports/property.xml
     and bucket every checked property by its CBMC property class
     (user assertion, memory safety, arithmetic, unwinding, ...).

Usage:
  python3 classify_assertions.py --proof-dir path/to/proofs/foo
  python3 classify_assertions.py --scan-root cbmc-metrics-workspace --output classified.csv
"""

import argparse
import csv
import json
import re
import sys
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import Any, Dict, List, Optional


# -------------------------------------------------------------------
# Axis A: source-level classification
# -------------------------------------------------------------------

# construct -> regex capturing the argument start
CONSTRUCTS = {
    "assume": re.compile(r"__CPROVER_assume\s*\("),
    "precondition": re.compile(r"(?:__CPROVER_precondition|CBMC_PRECONDITION)\s*\("),
    "assert": re.compile(r"(?<![_A-Za-z0-9])assert\s*\("),
    "cprover_assert": re.compile(r"__CPROVER_assert\s*\("),
    "postcondition": re.compile(
        r"(?:__CPROVER_postcondition|__CPROVER_ensures|POSTCONDITION)\s*\("
    ),
}

STUB_NAME_HINTS = ("stub", "model", "mock")
STUB_DIR_HINTS = ("stubs", "sources", "helpers", "proof-support")

INTENT_RULES = [
    ("pointer-validity", re.compile(
        r"__CPROVER_[rw]+_ok|IMPLIES|_is_valid|allocated", re.IGNORECASE)),
    ("null-check", re.compile(r"\bNULL\b")),
    ("bounds", re.compile(
        r"[<>]=?\s*|\b(?:size|len|length|capacity|count|MAX|BOUND)\b", re.IGNORECASE)),
    ("equality-range", re.compile(r"==")),
]


def strip_comments_and_strings(text: str) -> str:
    """Remove /* */ and // comments and string/char literals so matches
    only hit real code."""
    out = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == "/" and i + 1 < n and text[i + 1] == "*":
            j = text.find("*/", i + 2)
            i = n if j < 0 else j + 2
        elif c == "/" and i + 1 < n and text[i + 1] == "/":
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif c in "\"'":
            quote = c
            out.append(quote)
            i += 1
            while i < n and text[i] != quote:
                i += 2 if text[i] == "\\" else 1
            if i < n:
                out.append(quote)
                i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def extract_argument(text: str, open_paren_idx: int) -> str:
    """Return the text of the balanced parenthesized argument starting at
    open_paren_idx (which must point at '(')."""
    depth = 0
    for j in range(open_paren_idx, len(text)):
        if text[j] == "(":
            depth += 1
        elif text[j] == ")":
            depth -= 1
            if depth == 0:
                return text[open_paren_idx + 1:j]
    return text[open_paren_idx + 1:]


def classify_intent(arg: str) -> str:
    for label, pat in INTENT_RULES:
        if pat.search(arg):
            return label
    return "other"


def file_role(path: Path, proof_dir: Path) -> str:
    name = path.name.lower()
    if name.endswith("_harness.c") or name == f"{proof_dir.name.lower()}.c":
        return "harness"
    if any(h in name for h in STUB_NAME_HINTS):
        return "stub"
    if any(part.lower() in STUB_DIR_HINTS for part in path.parts):
        return "stub"
    return "source"


def scan_source_files(proof_dir: Path) -> Dict[str, Any]:
    counts: Dict[str, int] = {
        "assume_harness": 0, "assume_stub": 0, "assume_source": 0,
        "precondition_macros": 0,
        "assert_harness": 0, "assert_stub": 0, "assert_source": 0,
        "cprover_asserts": 0, "postconditions": 0,
        "intent_pointer-validity": 0, "intent_null-check": 0,
        "intent_bounds": 0, "intent_equality-range": 0, "intent_other": 0,
    }

    c_files = [p for p in proof_dir.rglob("*.c") if "build" not in p.parts]
    for f in c_files:
        try:
            text = strip_comments_and_strings(
                f.read_text(encoding="utf-8", errors="ignore"))
        except OSError:
            continue
        role = file_role(f, proof_dir)
        for construct, pat in CONSTRUCTS.items():
            for m in pat.finditer(text):
                arg = extract_argument(text, m.end() - 1)
                if construct == "assume":
                    counts[f"assume_{role}"] += 1
                    counts[f"intent_{classify_intent(arg)}"] += 1
                elif construct == "precondition":
                    counts["precondition_macros"] += 1
                    counts[f"intent_{classify_intent(arg)}"] += 1
                elif construct == "assert":
                    counts[f"assert_{role}"] += 1
                elif construct == "cprover_assert":
                    counts["cprover_asserts"] += 1
                elif construct == "postcondition":
                    counts["postconditions"] += 1

    # matches num_preconditions in the existing collectors
    counts["num_preconditions_equivalent"] = (
        counts["assume_harness"] + counts["assume_stub"]
        + counts["assume_source"] + counts["precondition_macros"]
    )
    return counts


# -------------------------------------------------------------------
# Axis B: result-level classification by CBMC property class
# -------------------------------------------------------------------

CLASS_GROUPS = {
    "assertion": "user_assertion",
    "precondition": "contract",
    "precondition_instance": "contract",
    "postcondition": "contract",
    "pointer_dereference": "memory_safety",
    "pointer_arithmetic": "memory_safety",
    "pointer": "memory_safety",
    "pointer_primitives": "memory_safety",
    "array_bounds": "memory_safety",
    "memory-leak": "memory_safety",
    "memory_leak": "memory_safety",
    "overflow": "arithmetic",
    "division-by-zero": "arithmetic",
    "division_by_zero": "arithmetic",
    "NaN": "arithmetic",
    "bit_count": "arithmetic",
    "shift": "arithmetic",
    "unwind": "unwinding",
}

STDLIB_FUNCS = {"memcpy", "memset", "memmove", "memcmp", "strlen", "strcpy",
                "strncpy", "strcmp", "strncmp", "malloc", "free"}

GROUP_NAMES = ["user_assertion", "contract", "memory_safety", "arithmetic",
               "unwinding", "stdlib_model", "other"]


def classify_property(prop_id: str, explicit_class: Optional[str] = None) -> str:
    """Map a property ID like 'func.pointer_dereference.5' (and optionally the
    explicit class attribute from property.xml) to a class group."""
    cls = explicit_class
    parts = prop_id.rsplit(".", 2)
    if cls is None and len(parts) == 3:
        cls = parts[1]
    func = parts[0].split(".")[-1] if parts else ""
    if func in STDLIB_FUNCS:
        return "stdlib_model"
    if cls in CLASS_GROUPS:
        return CLASS_GROUPS[cls]
    return "other"


def empty_prop_counts() -> Dict[str, int]:
    d: Dict[str, int] = {}
    for g in GROUP_NAMES:
        d[f"props_{g}_pass"] = 0
        d[f"props_{g}_fail"] = 0
    return d


def parse_viewer_result(proof_dir: Path) -> Optional[Dict[str, int]]:
    candidates = list(proof_dir.glob("report/json/viewer-result.json")) + \
        list(proof_dir.glob("build/report/json/viewer-result.json"))
    if not candidates:
        return None
    try:
        raw = json.loads(candidates[0].read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    vr = raw.get("viewer-result", raw)
    results = vr.get("results", {})
    if not isinstance(results, dict):
        return None

    counts = empty_prop_counts()
    for verdict, suffix in (("true", "pass"), ("false", "fail")):
        for prop in results.get(verdict) or []:
            group = classify_property(str(prop))
            counts[f"props_{group}_{suffix}"] += 1
    return counts


def parse_property_xml(proof_dir: Path) -> Optional[Dict[str, int]]:
    prop_xml = proof_dir / "build" / "reports" / "property.xml"
    if not prop_xml.is_file():
        return None
    try:
        root = ET.fromstring(prop_xml.read_text(encoding="utf-8", errors="ignore"))
    except (OSError, ET.ParseError):
        return None

    counts = empty_prop_counts()
    saw_any = False
    for pr in root.iter("property"):
        saw_any = True
        group = classify_property(pr.get("name") or "", pr.get("class"))
        status = (pr.get("status") or "").upper()
        suffix = "fail" if status == "FAILURE" else "pass"
        counts[f"props_{group}_{suffix}"] += 1
    return counts if saw_any else None


# -------------------------------------------------------------------
# Driver
# -------------------------------------------------------------------

def looks_like_proof_dir(d: Path) -> bool:
    if not d.is_dir():
        return False
    if not (d / "Makefile").is_file() and not any(d.glob("*_harness.c")):
        return False
    return any(d.glob("*.c"))


def classify_proof(proof_dir: Path) -> Dict[str, Any]:
    row: Dict[str, Any] = {
        "proof_id": proof_dir.name,
        "proof_path": str(proof_dir),
    }
    row.update(scan_source_files(proof_dir))
    prop_counts = parse_viewer_result(proof_dir) or parse_property_xml(proof_dir)
    row.update(prop_counts if prop_counts else empty_prop_counts())
    row["has_property_results"] = int(prop_counts is not None)
    return row


def main() -> None:
    ap = argparse.ArgumentParser(
        description="Classify assertions/assumptions in CBMC proof dirs.")
    ap.add_argument("--proof-dir", help="Classify exactly one proof directory.")
    ap.add_argument("--scan-root", help="Scan for proof directories under this root.")
    ap.add_argument("--output", help="Output CSV path (default: print to stdout).")
    args = ap.parse_args()

    if bool(args.proof_dir) == bool(args.scan_root):
        ap.error("provide exactly one of --proof-dir or --scan-root")

    if args.proof_dir:
        dirs = [Path(args.proof_dir)]
    else:
        root = Path(args.scan_root)
        dirs = sorted(d for d in root.rglob("*")
                      if looks_like_proof_dir(d) and "build" not in d.parts)
        # keep only leaf proof dirs (a proof dir containing another proof dir
        # is a parent folder, not a proof)
        dirs = [d for d in dirs
                if not any(other != d and other.is_relative_to(d) for other in dirs)]

    rows = [classify_proof(d) for d in dirs]
    if not rows:
        print("No proof directories found.", file=sys.stderr)
        sys.exit(1)

    fieldnames = list(rows[0].keys())
    if args.output:
        with open(args.output, "w", newline="", encoding="utf-8") as fh:
            w = csv.DictWriter(fh, fieldnames=fieldnames)
            w.writeheader()
            w.writerows(rows)
        print(f"Wrote {len(rows)} rows to {args.output}")
    else:
        w = csv.DictWriter(sys.stdout, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(rows)


if __name__ == "__main__":
    main()
