#!/usr/bin/env python3
"""
Collect CBMC + coverage metrics for AutoUP-generated proof leaf directories.

AutoUP layout (typical):
  <repo>/autoup-harnesses/<batch>/<module>/<proof>/
    - Makefile
    - *_harness.c
    - metrics.jsonl
    - build/reports/{cbmc.xml,property.xml,coverage.xml}
    - (optional) build/report/json/viewer-result.json
    - (optional) viewer-coverage*.json (ANYWHERE under proof; schema varies)

CSV columns:
repo,proof_id,proof_path,loc,files_in_scope,num_preconditions,num_var_models,num_func_models,
size_func_models_loc,symex_steps,sat_vars,sat_clauses,max_unwind,runtime_seconds,total_coverage,
target_coverage,harness_coverage,non_harness_coverage,num_errors

Key behavior:
- Always fills total_coverage/target_coverage from coverage.xml (overall)
- Fills harness_coverage/non_harness_coverage ONLY if viewer-coverage*.json exists AND contains
  per-file or per-line data
- Uses viewer-result.json for SAT/symex/runtime when available; falls back to cbmc.xml
- Proof ID normalized: batch16_fixed_symbols_abs_YYYYMMDD_HHMMSS -> basbs_YYYYMMDD_HHMMSS/<proof>
"""

import argparse
import csv
import json
import re
import sys
import xml.etree.ElementTree as ET
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, Union


CSV_COLUMNS = [
    "repo",
    "proof_id",
    "proof_path",
    "loc",
    "files_in_scope",
    "num_preconditions",
    "num_var_models",
    "num_func_models",
    "size_func_models_loc",
    "symex_steps",
    "sat_vars",
    "sat_clauses",
    "max_unwind",
    "runtime_seconds",
    "total_coverage",
    "target_coverage",
    "harness_coverage",
    "non_harness_coverage",
    "num_errors",
]


@dataclass
class ProofMetrics:
    repo: str
    proof_id: str
    proof_path: str

    loc: Optional[int] = None
    files_in_scope: Optional[int] = None
    num_preconditions: Optional[int] = None
    num_var_models: Optional[int] = None
    num_func_models: Optional[int] = None
    size_func_models_loc: Optional[int] = None

    symex_steps: Optional[int] = None
    sat_vars: Optional[int] = None
    sat_clauses: Optional[int] = None
    max_unwind: Optional[int] = None

    runtime_seconds: Optional[float] = None
    total_coverage: Optional[float] = None
    target_coverage: Optional[float] = None
    harness_coverage: Optional[float] = None
    non_harness_coverage: Optional[float] = None

    num_errors: Optional[int] = None

    def to_row(self) -> Dict[str, Any]:
        row = asdict(self)
        for c in CSV_COLUMNS:
            row.setdefault(c, None)
        return row


def safe_read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        return ""


# -------------------------
# proof_id normalization
# -------------------------

_RE_BATCH = re.compile(r"^batch\d+_fixed_symbols_abs_(\d{8}_\d{6})$")


def normalize_batch_dirname(batch_dirname: str) -> str:
    """
    batch16_fixed_symbols_abs_20260204_115414 -> basbs_20260204_115414
    otherwise, return batch_dirname unchanged.
    """
    m = _RE_BATCH.match(batch_dirname)
    if m:
        return f"basbs_{m.group(1)}"
    return batch_dirname


def compute_proof_id_autoup(proof_dir: Path) -> str:
    """
    For:
      .../autoup-harnesses/<batch>/<module>/<proof>
    Return:
      <normalized_batch>/<proof>
    """
    parts = proof_dir.resolve().parts
    if "autoup-harnesses" in parts:
        i = parts.index("autoup-harnesses")
        if len(parts) >= i + 4:
            batch = parts[i + 1]
            proof = parts[i + 3]
            return f"{normalize_batch_dirname(batch)}/{proof}"
    return proof_dir.name


# -------------------------
# static metrics from files
# -------------------------

def _is_comment_or_blank(line: str) -> bool:
    s = line.strip()
    if not s:
        return True
    if s.startswith("//") or s.startswith("/*") or s.startswith("*") or s.startswith("*/"):
        return True
    return False


def count_loc(files: List[Path]) -> int:
    loc = 0
    for f in files:
        for line in safe_read_text(f).splitlines():
            if _is_comment_or_blank(line):
                continue
            loc += 1
    return loc


def count_preconditions(files: List[Path]) -> int:
    pat = re.compile(r"__CPROVER_precondition|CBMC_PRECONDITION|__CPROVER_assume")
    c = 0
    for f in files:
        c += len(pat.findall(safe_read_text(f)))
    return c


def count_models(files: List[Path]) -> Tuple[int, int]:
    """
    var_models: nondet_*(
    func_models: *_stub or *_model (common naming)
    """
    var_pat = re.compile(r"\bnondet_[A-Za-z0-9_]+\s*\(")
    func_pat = re.compile(r"\b[A-Za-z_][A-Za-z0-9_]*_(?:stub|model)\b")

    var_models = 0
    func_models = 0

    for f in files:
        t = safe_read_text(f)
        var_models += len(var_pat.findall(t))
        func_models += len(func_pat.findall(t))

    return var_models, func_models


def select_modelish_files(files: List[Path]) -> List[Path]:
    """
    For size_func_models_loc:
      include *stubs*.c, *models*.c, general-stubs.c, and any file containing 'stub'/'model' in name
    """
    out: List[Path] = []
    for p in files:
        if p.suffix.lower() not in (".c", ".h"):
            continue
        n = p.name.lower()
        if n == "general-stubs.c" or "stub" in n or "model" in n or n.endswith(("models.c", "stubs.c")):
            out.append(p)

    seen = set()
    uniq: List[Path] = []
    for p in out:
        rp = str(p.resolve())
        if rp not in seen:
            seen.add(rp)
            uniq.append(p)
    return uniq


def gather_scope_files_autoup(proof_dir: Path) -> List[Path]:
    """
    Include:
      - all .c/.h in leaf dir (recursive)
      - in parent dir: general-stubs.c + any *stubs*.c/*models*.c (non-recursive)
    """
    leaf = list(proof_dir.rglob("*.c")) + list(proof_dir.rglob("*.h"))

    parent = proof_dir.parent
    parent_add: List[Path] = []
    if parent.is_dir():
        for p in parent.iterdir():
            if not p.is_file():
                continue
            if p.suffix.lower() not in (".c", ".h"):
                continue
            n = p.name.lower()
            if n == "general-stubs.c" or "stub" in n or "model" in n:
                parent_add.append(p)

    seen = set()
    out: List[Path] = []
    for p in leaf + parent_add:
        rp = str(p.resolve())
        if rp not in seen:
            seen.add(rp)
            out.append(p)
    return out


def parse_unwind_from_makefile(proof_dir: Path) -> Optional[int]:
    mk = proof_dir / "Makefile"
    if not mk.is_file():
        return None
    t = safe_read_text(mk)

    m = re.search(r"--unwind(?:\s+|=)(\d+)", t)
    if m:
        return int(m.group(1))

    m = re.search(r"^\s*UNWIND\s*[:?]?=\s*(\d+)\s*$", t, flags=re.MULTILINE)
    if m:
        return int(m.group(1))

    return None


# -------------------------
# viewer-result.json parsing
# -------------------------

def find_viewer_result_json(proof_dir: Path) -> Optional[Path]:
    for cand_dir in [
        proof_dir / "build" / "report" / "json",
        proof_dir / "report" / "json",
        proof_dir / "build" / "reports" / "json",
    ]:
        if cand_dir.is_dir():
            p = cand_dir / "viewer-result.json"
            if p.is_file():
                return p
            cands = sorted(cand_dir.glob("viewer-result*.json"))
            if cands:
                return cands[0]
    # bounded search
    try:
        cands = list(proof_dir.rglob("viewer-result*.json"))
        cands = [p for p in cands if p.is_file()]
        cands.sort()
        return cands[0] if cands else None
    except Exception:
        return None


def parse_viewer_result_json(proof_dir: Path) -> Dict[str, Any]:
    p = find_viewer_result_json(proof_dir)
    if p is None:
        return {}

    try:
        raw = json.loads(p.read_text(encoding="utf-8"))
    except Exception:
        return {}

    vr = raw.get("viewer-result", raw)
    stats: Dict[str, Any] = {}

    status_lines = vr.get("status") or []
    if isinstance(status_lines, str):
        status_lines = status_lines.splitlines()
    if not isinstance(status_lines, list):
        return stats

    # SAT vars/clauses
    last_vars = last_clauses = None
    for line in status_lines:
        m = re.search(r"([0-9,]+)\s+variables,\s*([0-9,]+)\s+clauses", str(line), flags=re.IGNORECASE)
        if m:
            last_vars, last_clauses = m.groups()
    if last_vars and last_clauses:
        stats["sat_vars"] = int(last_vars.replace(",", ""))
        stats["sat_clauses"] = int(last_clauses.replace(",", ""))

    # runtime
    for line in status_lines:
        m = re.search(r"Runtime decision procedure:\s*([0-9.]+)\s*s", str(line), flags=re.IGNORECASE)
        if m:
            stats["runtime_seconds"] = float(m.group(1))
            break

    # symex steps
    for line in status_lines:
        m = re.search(r"size of program expression:\s*([0-9,]+)\s+steps", str(line), flags=re.IGNORECASE)
        if m:
            stats["symex_steps"] = int(m.group(1).replace(",", ""))
            break

    # max unwind (fallback)
    max_it = None
    for line in status_lines:
        m = re.search(r"Not unwinding loop .* iteration\s+(\d+)", str(line), flags=re.IGNORECASE)
        if m:
            it = int(m.group(1))
            max_it = it if max_it is None else max(max_it, it)
    if max_it is not None:
        stats["max_unwind"] = max_it

    return stats


# -------------------------
# CBMC XML parsing
# -------------------------

def _xml_messages(xml_path: Path) -> List[str]:
    try:
        root = ET.fromstring(xml_path.read_text(encoding="utf-8", errors="ignore"))
    except Exception:
        return []
    out: List[str] = []
    for msg in root.iter("message"):
        t = (msg.text or "").strip()
        if t:
            out.append(t)
    return out


def parse_property_xml_num_errors(proof_dir: Path) -> Optional[int]:
    prop = proof_dir / "build" / "reports" / "property.xml"
    if not prop.is_file():
        return None

    try:
        root = ET.fromstring(prop.read_text(encoding="utf-8", errors="ignore"))
    except Exception:
        return None

    failures = 0
    saw_any = False
    for pr in root.iter("property"):
        saw_any = True
        status = (pr.get("status") or "").upper()
        if status == "FAILURE":
            failures += 1

    return failures if saw_any else None


def parse_cbmc_xml_stats(proof_dir: Path) -> Dict[str, Any]:
    cbmc = proof_dir / "build" / "reports" / "cbmc.xml"
    if not cbmc.is_file():
        return {}

    lines = _xml_messages(cbmc)
    stats: Dict[str, Any] = {}

    last_vars = last_clauses = None
    for line in lines:
        m = re.search(r"([0-9,]+)\s+variables,\s*([0-9,]+)\s+clauses", line, flags=re.IGNORECASE)
        if m:
            last_vars, last_clauses = m.groups()
    if last_vars and last_clauses:
        stats["sat_vars"] = int(last_vars.replace(",", ""))
        stats["sat_clauses"] = int(last_clauses.replace(",", ""))

    for line in lines:
        m = re.search(r"Runtime decision procedure:\s*([0-9.]+)\s*s", line, flags=re.IGNORECASE)
        if m:
            stats["runtime_seconds"] = float(m.group(1))
            break

    for line in lines:
        m = re.search(r"size of program expression:\s*([0-9,]+)\s+steps", line, flags=re.IGNORECASE)
        if m:
            stats["symex_steps"] = int(m.group(1).replace(",", ""))
            break

    max_it = None
    for line in lines:
        m = re.search(r"Not unwinding loop .* iteration\s+(\d+)", line, flags=re.IGNORECASE)
        if m:
            it = int(m.group(1))
            max_it = it if max_it is None else max(max_it, it)
    if max_it is not None:
        stats["max_unwind"] = max_it

    return stats


# -------------------------
# Coverage parsing
# -------------------------

def parse_coverage_xml_overall(proof_dir: Path) -> Dict[str, Any]:
    """
    Overall coverage extraction from build/reports/coverage.xml.
    Treat overall = total_coverage = target_coverage.
    """
    cov = proof_dir / "build" / "reports" / "coverage.xml"
    if not cov.is_file():
        return {}

    try:
        root = ET.fromstring(cov.read_text(encoding="utf-8", errors="ignore"))
    except Exception:
        return {}

    blob = " ".join((t or "") for t in root.itertext())
    m = re.search(r"overall.*?([0-9]+(?:\.[0-9]+)?)\s*%", blob, flags=re.IGNORECASE | re.DOTALL)
    if not m:
        m = re.search(r"([0-9]+(?:\.[0-9]+)?)\s*%", blob)
    if not m:
        return {}

    pct = float(m.group(1))
    return {"total_coverage": pct, "target_coverage": pct}


def find_viewer_coverage_json(proof_dir: Path) -> Optional[Path]:
    # expected first
    for cand_dir in [
        proof_dir / "build" / "report" / "json",
        proof_dir / "report" / "json",
        proof_dir / "build" / "reports" / "json",
    ]:
        if cand_dir.is_dir():
            p = cand_dir / "viewer-coverage.json"
            if p.is_file():
                return p
            cands = sorted(cand_dir.glob("viewer-coverage*.json"))
            if cands:
                return cands[0]

    # bounded search
    try:
        cands = list(proof_dir.rglob("viewer-coverage*.json"))
        cands = [p for p in cands if p.is_file()]
        cands.sort()
        return cands[0] if cands else None
    except Exception:
        return None


def compute_split_coverage_from_viewer_coverage_json(
    proof_dir: Path,
    proof_id: str,
) -> Dict[str, float]:
    """
    Supports cbmc-viewer schema:
      viewer-coverage.json -> { "viewer-coverage": { "line_coverage": { file: { line: "hit"/... }}}}

    Returns:
      harness_coverage, non_harness_coverage in 0..100
    """
    cov_path = find_viewer_coverage_json(proof_dir)
    if cov_path is None:
        return {}

    try:
        raw = json.loads(cov_path.read_text(encoding="utf-8"))
    except Exception:
        return {}

    vc = raw.get("viewer-coverage", raw)

    # Some versions: vc["line_coverage"] = { file -> { line -> "hit"/... } }
    line_cov = vc.get("line_coverage")
    if not isinstance(line_cov, dict) or not line_cov:
        return {}

    harness_cov = harness_total = 0
    non_cov = non_total = 0

    harness_leaf_names = {p.name.lower() for p in proof_dir.glob("*harness*.c")}
    proof_leaf = proof_id.strip("/").split("/")[-1].lower()

    for file_path, lines in line_cov.items():
        if not isinstance(lines, dict):
            continue
        total = len(lines)
        covered = sum(1 for status in lines.values() if str(status).lower() == "hit")

        fp = str(file_path).replace("\\", "/").lower()
        base = Path(fp).name.lower()

        is_harness = (base in harness_leaf_names) or (("harness" in fp) and (proof_leaf in fp))

        if is_harness:
            harness_total += total
            harness_cov += covered
        else:
            non_total += total
            non_cov += covered

    out: Dict[str, float] = {}
    if harness_total:
        out["harness_coverage"] = 100.0 * harness_cov / harness_total
    if non_total:
        out["non_harness_coverage"] = 100.0 * non_cov / non_total
    return out


# -------------------------
# main collection
# -------------------------

def append_row(pm: ProofMetrics, out_csv: Path) -> None:
    out_csv.parent.mkdir(parents=True, exist_ok=True)
    write_header = (not out_csv.exists()) or out_csv.stat().st_size == 0
    with out_csv.open("a", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=CSV_COLUMNS, extrasaction="ignore")
        if write_header:
            w.writeheader()
        w.writerow(pm.to_row())


def is_autoup_leaf_dir(d: Path) -> bool:
    if not d.is_dir():
        return False
    if not (d / "Makefile").is_file():
        return False
    if not (d / "build" / "reports").is_dir():
        return False
    if list(d.glob("*harness*.c")) or (d / "metrics.jsonl").is_file():
        return True
    return True


def collect_one(proof_dir: Path, repo: str) -> ProofMetrics:
    proof_dir = proof_dir.expanduser().resolve()

    pm = ProofMetrics(
        repo=repo,
        proof_id=compute_proof_id_autoup(proof_dir),
        proof_path=str(proof_dir),
    )

    scope = gather_scope_files_autoup(proof_dir)
    scope_c = [p for p in scope if p.suffix.lower() == ".c"]
    scope_ch = [p for p in scope if p.suffix.lower() in (".c", ".h")]

    harness = list(proof_dir.glob("*harness*.c"))
    if harness:
        pm.loc = count_loc(harness)
    elif scope_c:
        pm.loc = count_loc(scope_c)
    else:
        pm.loc = 0

    pm.files_in_scope = len(scope_c) if scope_c else 0
    pm.num_preconditions = count_preconditions(scope_c) if scope_c else 0

    vm, fm = count_models(scope_c) if scope_c else (0, 0)
    pm.num_var_models = vm
    pm.num_func_models = fm

    modelish = select_modelish_files(scope_ch)
    pm.size_func_models_loc = count_loc(modelish) if modelish else 0

    pm.max_unwind = parse_unwind_from_makefile(proof_dir)

    # stats: viewer-result first
    vr = parse_viewer_result_json(proof_dir)
    for k in ("symex_steps", "sat_vars", "sat_clauses", "runtime_seconds", "max_unwind"):
        if getattr(pm, k) is None and vr.get(k) is not None:
            setattr(pm, k, vr[k])

    # fallback: cbmc.xml
    cx = parse_cbmc_xml_stats(proof_dir)
    for k in ("symex_steps", "sat_vars", "sat_clauses", "runtime_seconds", "max_unwind"):
        if getattr(pm, k) is None and cx.get(k) is not None:
            setattr(pm, k, cx[k])

    pm.num_errors = parse_property_xml_num_errors(proof_dir)
    if pm.num_errors is None:
        pm.num_errors = 0

    cov = parse_coverage_xml_overall(proof_dir)
    if cov.get("total_coverage") is not None:
        pm.total_coverage = float(cov["total_coverage"])
    if cov.get("target_coverage") is not None:
        pm.target_coverage = float(cov["target_coverage"])

    # Split coverage: ONLY if viewer-coverage exists and has line_coverage
    split = compute_split_coverage_from_viewer_coverage_json(proof_dir, pm.proof_id)
    if split.get("harness_coverage") is not None:
        pm.harness_coverage = float(split["harness_coverage"])
    if split.get("non_harness_coverage") is not None:
        pm.non_harness_coverage = float(split["non_harness_coverage"])

    return pm


def scan_and_collect(root: Path, repo: str, out_csv: Path) -> int:
    root = root.expanduser().resolve()
    n = 0
    for d in sorted(root.rglob("*")):
        if is_autoup_leaf_dir(d):
            pm = collect_one(d, repo)
            append_row(pm, out_csv)
            n += 1
    return n


def main() -> None:
    ap = argparse.ArgumentParser(description="Collect metrics for AutoUP proof directories.")
    ap.add_argument("--repo", required=True, help="Repo label for CSV, e.g. FreeRTOS/FreeRTOS-Plus-TCP")
    ap.add_argument("--proof-dir", help="Collect for exactly one AutoUP proof leaf directory.")
    ap.add_argument("--scan-root", help="Scan under this directory and collect all AutoUP leaf proofs found.")
    ap.add_argument("--output", default="autoup_metrics.csv", help="Output CSV path.")
    args = ap.parse_args()

    out_csv = Path(args.output).expanduser().resolve()

    if not args.proof_dir and not args.scan_root:
        print("[ERROR] Provide --proof-dir or --scan-root", file=sys.stderr)
        sys.exit(2)

    if args.proof_dir:
        pd = Path(args.proof_dir)
        if not pd.is_dir():
            raise FileNotFoundError(f"--proof-dir is not a directory: {pd}")
        pm = collect_one(pd, args.repo)
        append_row(pm, out_csv)
        print(f"[OK] wrote 1 row -> {out_csv}")
        print(f"[OK] proof_id={pm.proof_id}")
        return

    sr = Path(args.scan_root)
    if not sr.is_dir():
        raise FileNotFoundError(f"--scan-root is not a directory: {sr}")
    n = scan_and_collect(sr, args.repo, out_csv)
    print(f"[OK] wrote {n} rows -> {out_csv}")


if __name__ == "__main__":
    main()
