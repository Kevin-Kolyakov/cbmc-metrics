#!/usr/bin/env python3
import argparse
import csv
import json
import os
import re
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import List, Optional, Dict, Any, Tuple, Set, Union


# Default repos list (override with --repo or --repo-dir)
REPOS = [
    "pq-code-package/mlkem-native",
]

SKIP_PROOFS: Set[str] = set()
ATTEMPT_MARKER = ".cbmc_attempted"


# -------- regex for stats parsing (viewer-result.json status lines or logs/stats.txt) --------
RE_SYMEX_STEPS = re.compile(r"size of program expression:\s*([0-9,]+)\s*steps", re.IGNORECASE)
RE_VARS_CLAUSES = re.compile(r"([0-9,]+)\s+variables,\s*([0-9,]+)\s+clauses", re.IGNORECASE)
RE_DP_RUNTIME = re.compile(r"Runtime decision procedure:\s*([0-9.]+)\s*s", re.IGNORECASE)
RE_MAX_UNWIND_ITER = re.compile(r"Unwinding loop .* iteration\s+([0-9]+)\b", re.IGNORECASE)


@dataclass
class ProofMetrics:
    repo: str
    proof_id: str          # relative path like proofs/cbmc/foo
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
        return asdict(self)


def _as_text(x: Union[str, bytes, None]) -> str:
    if x is None:
        return ""
    if isinstance(x, bytes):
        return x.decode("utf-8", errors="replace")
    return x


def safe_read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        return ""


def normalize_pct(x: float) -> float:
    return x * 100.0 if x <= 1.0 else x


def load_completed_keys(csv_path: Path) -> Set[Tuple[str, str]]:
    completed: Set[Tuple[str, str]] = set()
    if not csv_path.exists() or csv_path.stat().st_size == 0:
        return completed
    try:
        with csv_path.open("r", newline="", encoding="utf-8") as f:
            reader = csv.DictReader(f)
            if not reader.fieldnames:
                return completed
            for row in reader:
                r = (row.get("repo") or "").strip()
                p = (row.get("proof_id") or "").strip()
                if r and p:
                    completed.add((r, p))
    except Exception as e:
        print(f"[WARN] Could not read existing CSV for resume: {csv_path} ({e})")
    return completed


def git_clone(repo: str, dest_root: Path, skip_if_exists: bool = True) -> Path:
    owner, name = repo.split("/")
    repo_dir = dest_root / name
    if repo_dir.exists() and skip_if_exists:
        print(f"[INFO] Repo already exists, skipping clone: {repo_dir}")
        return repo_dir

    if repo_dir.exists():
        shutil.rmtree(repo_dir)

    url = f"https://github.com/{repo}.git"
    print(f"[INFO] Cloning {url} into {repo_dir}")
    result = subprocess.run(
        ["git", "clone", "--depth", "1", url, str(repo_dir)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if result.returncode != 0:
        raise RuntimeError(f"git clone failed for {repo}:\n{result.stdout}\n{result.stderr}")
    return repo_dir


def rel_proof_id(repo_root: Path, proof_dir: Path) -> str:
    try:
        return str(proof_dir.resolve().relative_to(repo_root.resolve())).replace("\\", "/")
    except Exception:
        return proof_dir.name



def is_leaf_proof_dir(d: Path) -> bool:
    if not d.is_dir():
        return False
    # primary indicator: Makefile
    if (d / "Makefile").is_file():
        return True
    # secondary: harness files
    for p in d.glob("*.c"):
        if "harness" in p.name.lower():
            return True
    # tertiary: viewer json already present
    json_dir = d / "report" / "json"
    if (json_dir / "viewer-result.json").is_file() or (json_dir / "viewer-coverage.json").is_file():
        return True
    return False


def find_proof_dirs(repo_root: Path) -> List[Path]:
    candidates: List[Path] = []

    preferred_roots = [
        repo_root / "test" / "cbmc" / "proofs",
        repo_root / "verification" / "cbmc" / "proofs",
        repo_root / "proofs" / "cbmc",  # mlkem-native layout
    ]

    for root in preferred_roots:
        if root.is_dir():
            for d in root.rglob("*"):
                if is_leaf_proof_dir(d):
                    candidates.append(d)

    # fallback: cbmc/proofs anywhere
    for cbmc_dir in repo_root.rglob("cbmc"):
        pr = cbmc_dir / "proofs"
        if pr.is_dir():
            for d in pr.rglob("*"):
                if is_leaf_proof_dir(d):
                    candidates.append(d)

    uniq: Dict[Path, None] = {}
    for p in candidates:
        uniq[p.resolve()] = None
    return sorted(uniq.keys(), key=lambda x: str(x))


def count_lines_of_code(files: List[Path]) -> int:
    loc = 0
    for f in files:
        for line in safe_read_text(f).splitlines():
            stripped = line.strip()
            if not stripped:
                continue
            # simple comment filters (good enough for your metric)
            if stripped.startswith("//") or stripped.startswith("/*") or stripped.startswith("*"):
                continue
            loc += 1
    return loc


def count_preconditions_in_files(files: List[Path]) -> int:
    pattern = re.compile(r"__CPROVER_precondition|CBMC_PRECONDITION|__CPROVER_assume")
    count = 0
    for f in files:
        count += len(pattern.findall(safe_read_text(f)))
    return count


def count_models_in_files(files: List[Path]) -> Tuple[int, int]:
    # best-effort heuristics
    var_pattern = re.compile(r"\bnondet_[a-zA-Z0-9_]+\s*\(")
    func_decl_pattern = re.compile(
        r"\b[a-zA-Z_][a-zA-Z0-9_]*_stub\b|\b[a-zA-Z_][a-zA-Z0-9_]*_model\b"
    )
    var_models = 0
    func_models = 0
    for f in files:
        text = safe_read_text(f)
        var_models += len(var_pattern.findall(text))
        func_models += len(func_decl_pattern.findall(text))
        if f.name.lower().endswith(("stubs.c", "models.c")):
            func_models += 1
    return var_models, func_models


def identify_function_model_files(files: List[Path]) -> List[Path]:
    model_files: List[Path] = []
    for f in files:
        name = f.name.lower()
        p = str(f).replace("\\", "/").lower()

        if name.endswith(("stubs.c", "models.c")):
            model_files.append(f)
            continue
        if "/stubs/" in p or "/models/" in p:
            model_files.append(f)
            continue
        if "stub" in name or "model" in name:
            model_files.append(f)
            continue

        text = safe_read_text(f)
        if re.search(r"\b[a-zA-Z_][a-zA-Z0-9_]*_(stub|model)\b", text):
            model_files.append(f)

    seen = set()
    out: List[Path] = []
    for f in model_files:
        rp = f.resolve()
        if rp not in seen:
            seen.add(rp)
            out.append(f)
    return out


def load_skip_list(path: Path) -> Set[str]:
    out: Set[str] = set()
    if not path.exists():
        raise FileNotFoundError(f"Skip list file not found: {path}")
    for line in safe_read_text(path).splitlines():
        s = line.strip()
        if not s or s.startswith("#"):
            continue
        out.add(s.rstrip("/"))
    return out


def get_viewer_json_dir(proof_dir: Path) -> Optional[Path]:
    # common
    p1 = proof_dir / "report" / "json"
    if p1.is_dir():
        return p1

    # sometimes produced in build dirs
    for cand in [
        proof_dir / "build" / "report" / "json",
        proof_dir / "build" / "reports" / "json",
    ]:
        if cand.is_dir():
            return cand

    # last resort: find any viewer-result*.json under proof
    try:
        found = next(proof_dir.rglob("viewer-result*.json"), None)
    except Exception:
        found = None
    if found and found.is_file():
        return found.parent

    return None


def compute_split_coverage_from_viewer(json_dir: Path, proof_id: str) -> Dict[str, float]:
    cov_path = json_dir / "viewer-coverage.json"
    if not cov_path.is_file():
        cands = sorted(json_dir.glob("viewer-coverage*.json"))
        if not cands:
            return {}
        cov_path = cands[0]

    try:
        raw = json.loads(cov_path.read_text(encoding="utf-8"))
    except Exception:
        return {}

    vc = raw.get("viewer-coverage", raw)
    line_cov = vc.get("line_coverage")
    if not isinstance(line_cov, dict) or not line_cov:
        return {}

    harness_cov = harness_total = 0
    non_cov = non_total = 0

    leaf = proof_id.strip("/").split("/")[-1].lower()
    ml_frag = f"proofs/cbmc/{leaf}/"

    for file_path, lines in line_cov.items():
        if not isinstance(lines, dict):
            continue
        total = len(lines)
        covered = sum(1 for status in lines.values() if str(status).lower() == "hit")

        fp = str(file_path).replace("\\", "/").lower()
        # heuristic: harness files *within the proof dir path fragment*
        is_harness = ("harness" in fp) and (ml_frag in fp)

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


def parse_viewer_coverage_json(json_dir: Path, proof_id: str) -> Dict[str, Any]:
    cov_path = json_dir / "viewer-coverage.json"
    if not cov_path.is_file():
        cands = sorted(json_dir.glob("viewer-coverage*.json"))
        if not cands:
            return {}
        cov_path = cands[0]

    try:
        raw = json.loads(cov_path.read_text(encoding="utf-8"))
    except Exception:
        return {}

    vc = raw.get("viewer-coverage", raw)
    stats: Dict[str, Any] = {}

    overall = vc.get("overall_coverage")
    if isinstance(overall, dict) and "percentage" in overall:
        try:
            pct = normalize_pct(float(overall["percentage"]))
            stats["total_coverage"] = pct
            # if you don’t have a per-target number, mirror overall
            stats["target_coverage"] = pct
        except Exception:
            pass

    stats.update(compute_split_coverage_from_viewer(json_dir, proof_id))
    return stats


def parse_viewer_result_json(json_dir: Path) -> Dict[str, Any]:
    result_path = json_dir / "viewer-result.json"
    if not result_path.is_file():
        cands = sorted(json_dir.glob("viewer-result*.json"))
        if not cands:
            return {}
        result_path = cands[0]

    try:
        raw = json.loads(result_path.read_text(encoding="utf-8"))
    except Exception:
        return {}

    vr = raw.get("viewer-result", raw)
    stats: Dict[str, Any] = {}

    results = vr.get("results", {})
    false_props = results.get("false") or []
    if isinstance(false_props, list):
        stats["num_errors"] = len(false_props)

    status_lines = vr.get("status") or []
    if isinstance(status_lines, str):
        status_lines = status_lines.splitlines()

    last_vars = last_clauses = None
    for line in status_lines:
        m = RE_VARS_CLAUSES.search(line)
        if m:
            last_vars, last_clauses = m.groups()
    if last_vars and last_clauses:
        stats["sat_vars"] = int(last_vars.replace(",", ""))
        stats["sat_clauses"] = int(last_clauses.replace(",", ""))

    for line in status_lines:
        m = RE_DP_RUNTIME.search(line)
        if m:
            stats["runtime_seconds"] = float(m.group(1))
            break

    for line in status_lines:
        m = RE_SYMEX_STEPS.search(line)
        if m:
            stats["symex_steps"] = int(m.group(1).replace(",", ""))
            break

    # max_unwind is often absent in viewer json; keep for stats-pass
    return stats



def run_cbmc_for_proof(proof_dir: Path, timeout_seconds: int) -> Tuple[Optional[float], str, bool]:
    makefile = proof_dir / "Makefile"
    if not makefile.exists():
        print(f"[INFO] No Makefile in {proof_dir}, skipping CBMC run.")
        return None, "", False

    # ensure logs exists so tee/other scripts don't explode
    (proof_dir / "logs").mkdir(exist_ok=True)

    env = os.environ.copy()

    targets = [
        ["make", "report"],
        ["make", "coverage"],
        ["make", "viewer"],
        ["make", "goto"],
        ["make"],
    ]

    start = time.time()
    last_out = ""
    for cmd in targets:
        print(f"[INFO] Running '{' '.join(cmd)}' in {proof_dir} (timeout={timeout_seconds}s)")
        try:
            result = subprocess.run(
                cmd,
                cwd=str(proof_dir),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                env=env,
                timeout=timeout_seconds,
            )
            last_out = _as_text(result.stdout) + "\n" + _as_text(result.stderr)
            if result.returncode == 0:
                elapsed = time.time() - start
                print(f"[INFO] '{' '.join(cmd)}' finished in {elapsed:.2f}s")
                return elapsed, last_out, False
            else:
                print(f"[WARN] '{' '.join(cmd)}' failed (exit {result.returncode}). Trying next target.")
        except subprocess.TimeoutExpired as e:
            elapsed = time.time() - start
            out = _as_text(e.stdout) + "\n" + _as_text(e.stderr)
            print(f"[WARN] Timeout after {timeout_seconds}s; skipping proof: {proof_dir}")
            return elapsed, out, True

    elapsed = time.time() - start
    print(f"[WARN] All make targets failed in {proof_dir}.")
    return elapsed, last_out, False


# -----------------------------
# Stats-pass fallback
# -----------------------------
def find_latest_goto(proof_dir: Path) -> Optional[Path]:
    search_dirs = [proof_dir, proof_dir / "build", proof_dir / "gotos", proof_dir / "out"]
    gotos: List[Path] = []
    for d in search_dirs:
        if d.is_dir():
            try:
                gotos.extend(list(d.rglob("*.goto")))
            except Exception:
                pass
    if not gotos:
        return None
    gotos.sort(key=lambda p: p.stat().st_mtime, reverse=True)
    return gotos[0]


def run_stats_pass_cbmc(proof_dir: Path, goto_path: Path, timeout_seconds: int) -> Optional[Path]:
    logs_dir = proof_dir / "logs"
    logs_dir.mkdir(exist_ok=True)
    stats_path = logs_dir / "stats.txt"

    # reuse if newer than goto
    try:
        if stats_path.exists() and stats_path.stat().st_mtime >= goto_path.stat().st_mtime:
            return stats_path
    except Exception:
        pass

    base_flags = [
        "--verbosity", "8",
        "--trace",
        "--stop-on-fail",
        str(goto_path),
    ]

    attempts = [
        ["cbmc", "--sat-solver", "cadical"] + base_flags,
        ["cbmc", "--sat-solver", "minisat2"] + base_flags,
        ["cbmc"] + base_flags,
    ]

    for cmd in attempts:
        try:
            with stats_path.open("w", encoding="utf-8", errors="replace") as f:
                subprocess.run(
                    cmd,
                    cwd=str(proof_dir),
                    stdout=f,
                    stderr=subprocess.STDOUT,
                    text=True,
                    env=os.environ.copy(),
                    timeout=timeout_seconds,
                )
            return stats_path
        except FileNotFoundError:
            print("[WARN] cbmc not found in PATH; cannot run stats pass.")
            return None
        except subprocess.TimeoutExpired:
            try:
                with stats_path.open("a", encoding="utf-8", errors="replace") as f:
                    f.write("\n[WARN] stats pass timed out\n")
            except Exception:
                pass
            return stats_path
        except Exception:
            continue

    return stats_path if stats_path.exists() else None


def parse_stats_txt(stats_path: Path) -> Dict[str, Any]:
    text = safe_read_text(stats_path)
    out: Dict[str, Any] = {}

    m = RE_SYMEX_STEPS.search(text)
    if m:
        out["symex_steps"] = int(m.group(1).replace(",", ""))

    m = RE_VARS_CLAUSES.search(text)
    if m:
        out["sat_vars"] = int(m.group(1).replace(",", ""))
        out["sat_clauses"] = int(m.group(2).replace(",", ""))

    max_u = -1
    for mm in RE_MAX_UNWIND_ITER.finditer(text):
        try:
            it = int(mm.group(1))
            if it > max_u:
                max_u = it
        except Exception:
            pass
    if max_u >= 0:
        out["max_unwind"] = max_u

    m = RE_DP_RUNTIME.search(text)
    if m:
        out["runtime_seconds_dp"] = float(m.group(1))

    return out


# -----------------------------
# Per-proof collection
# -----------------------------
def collect_metrics_for_proof(
    repo_name: str,
    repo_root: Path,
    proof_dir: Path,
    run_cbmc_flag: bool = False,
    timeout_seconds: int = 120,
    stats_timeout_seconds: int = 300,
) -> Optional[ProofMetrics]:
    proof_id = rel_proof_id(repo_root, proof_dir)
    metrics = ProofMetrics(repo=repo_name, proof_id=proof_id, proof_path=str(proof_dir))

    all_c_files = list(proof_dir.rglob("*.c"))

    harness_files = [p for p in all_c_files if "harness" in p.name.lower()]
    if not harness_files:
        harness_files = all_c_files
    if harness_files:
        metrics.loc = count_lines_of_code(harness_files)

    if all_c_files:
        metrics.files_in_scope = len(all_c_files)
        metrics.num_preconditions = count_preconditions_in_files(all_c_files)
        vm, fm = count_models_in_files(all_c_files)
        metrics.num_var_models = vm
        metrics.num_func_models = fm
        model_files = identify_function_model_files(all_c_files)
        metrics.size_func_models_loc = count_lines_of_code(model_files) if model_files else 0

    # 1) run make targets (generates gotos and report/json)
    if run_cbmc_flag:
        elapsed, _out, timed_out = run_cbmc_for_proof(proof_dir, timeout_seconds)
        if timed_out:
            return None
        if elapsed is not None:
            metrics.runtime_seconds = round(elapsed, 3)

    # 2) parse viewer json (coverage + errors + maybe sat/symex/runtime)
    json_dir = get_viewer_json_dir(proof_dir)
    if json_dir is not None:
        cov_stats = parse_viewer_coverage_json(json_dir, proof_id)
        for k in ("total_coverage", "target_coverage", "harness_coverage", "non_harness_coverage"):
            v = cov_stats.get(k)
            if v is not None:
                setattr(metrics, k, v)

        res_stats = parse_viewer_result_json(json_dir)
        for k, v in res_stats.items():
            if k == "runtime_seconds" and metrics.runtime_seconds is not None:
                continue
            if v is not None:
                setattr(metrics, k, v)

    # 3) If missing SAT/symex, try logs/stats.txt (may exist from prior runs)
    if metrics.symex_steps is None or metrics.sat_vars is None or metrics.sat_clauses is None:
        stats_path = proof_dir / "logs" / "stats.txt"
        if stats_path.is_file():
            sp = parse_stats_txt(stats_path)
            for k in ("symex_steps", "sat_vars", "sat_clauses", "max_unwind"):
                if getattr(metrics, k) is None and sp.get(k) is not None:
                    setattr(metrics, k, sp[k])

    # 4) If still missing and a .goto exists, do a stats-pass cbmc run
    if metrics.symex_steps is None or metrics.sat_vars is None or metrics.sat_clauses is None:
        goto = find_latest_goto(proof_dir)
        if goto is not None:
            stats_path = run_stats_pass_cbmc(proof_dir, goto, stats_timeout_seconds)
            if stats_path is not None and stats_path.is_file():
                sp = parse_stats_txt(stats_path)
                for k in ("symex_steps", "sat_vars", "sat_clauses", "max_unwind"):
                    if getattr(metrics, k) is None and sp.get(k) is not None:
                        setattr(metrics, k, sp[k])

    return metrics


def append_metrics_row(metrics: ProofMetrics, output_path: Path) -> None:
    row = metrics.to_row()
    fieldnames = [
        "repo","proof_id","proof_path","loc","files_in_scope","num_preconditions",
        "num_var_models","num_func_models","size_func_models_loc",
        "symex_steps","sat_vars","sat_clauses","max_unwind","runtime_seconds",
        "total_coverage","target_coverage","harness_coverage","non_harness_coverage","num_errors"
    ]
    write_header = (not output_path.exists()) or (output_path.stat().st_size == 0)
    with output_path.open("a", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        if write_header:
            writer.writeheader()
        # ensure stable column ordering
        writer.writerow({k: row.get(k) for k in fieldnames})


def collect_metrics_for_repo(
    repo: str,
    workspace: Path,
    repo_dir_override: Optional[Path] = None,
    skip_clone: bool = False,
    run_cbmc_flag: bool = False,
    proof_filter: Optional[str] = None,
    output_path: Optional[Path] = None,
    timeout_seconds: int = 120,
    stats_timeout_seconds: int = 300,
    completed_keys: Optional[Set[Tuple[str, str]]] = None,
    skip_proofs: Optional[Set[str]] = None,
    skip_attempted: bool = False,
    mark_attempted: bool = False,
) -> List[ProofMetrics]:
    if repo_dir_override is not None:
        repo_dir = repo_dir_override.expanduser().resolve()
        if not repo_dir.exists():
            raise FileNotFoundError(f"--repo-dir does not exist: {repo_dir}")
    else:
        if skip_clone:
            _, name = repo.split("/")
            repo_dir = (workspace / name).resolve()
            if not repo_dir.exists():
                raise FileNotFoundError(f"Repo directory does not exist and --skip-clone is set: {repo_dir}")
        else:
            repo_dir = git_clone(repo, workspace, skip_if_exists=True)

    proof_dirs = find_proof_dirs(repo_dir)

    if proof_filter:
        pf = proof_filter.strip().rstrip("/")
        filtered = []
        for pd in proof_dirs:
            rid = rel_proof_id(repo_dir, pd).rstrip("/")
            if pd.name == pf or rid == pf or rid.endswith("/" + pf):
                filtered.append(pd)
        proof_dirs = filtered

    if not proof_dirs:
        print(f"[WARN] No proof directories found in {repo_dir}")
        return []

    completed_keys = completed_keys or set()
    skip_proofs = skip_proofs or set()

    metrics_list: List[ProofMetrics] = []
    for pd in proof_dirs:
        pid = rel_proof_id(repo_dir, pd)
        base = Path(pid).name

        if pid in skip_proofs or base in skip_proofs:
            print(f"[INFO] Skipping proof (in skip list): {repo} / {pid}")
            continue

        if (repo, pid) in completed_keys:
            print(f"[INFO] Skipping already-completed proof: {repo} / {pid}")
            continue

        marker_path = pd / ATTEMPT_MARKER
        if skip_attempted and marker_path.exists():
            print(f"[INFO] Skipping already-attempted proof (marker): {repo} / {pid}")
            continue

        try:
            pm = collect_metrics_for_proof(
                repo_name=repo,
                repo_root=repo_dir,
                proof_dir=pd,
                run_cbmc_flag=run_cbmc_flag,
                timeout_seconds=timeout_seconds,
                stats_timeout_seconds=stats_timeout_seconds,
            )

            if mark_attempted:
                try:
                    marker_path.write_text("attempted\n", encoding="utf-8")
                except Exception as e:
                    print(f"[WARN] Could not write attempt marker {marker_path}: {e}")

            if pm is None:
                continue

            metrics_list.append(pm)
            if output_path is not None:
                append_metrics_row(pm, output_path)
                completed_keys.add((repo, pid))

        except Exception as e:
            if mark_attempted:
                try:
                    marker_path.write_text("attempted\n", encoding="utf-8")
                except Exception as e2:
                    print(f"[WARN] Could not write attempt marker {marker_path}: {e2}")
            print(f"[ERROR] Failed to collect metrics for {repo} / {pd}: {e}", file=sys.stderr)

    return metrics_list


def main() -> None:
    parser = argparse.ArgumentParser(description="Collect CBMC proof metrics (mlkem-native friendly).")
    parser.add_argument("--workspace", type=str, default="cbmc-metrics-workspace")
    parser.add_argument("--repo", type=str, action="append")
    parser.add_argument("--repo-dir", type=str, default=None, help="Explicit local repo path (use with local/* repo name).")

    parser.add_argument("--skip-clone", action="store_true")
    parser.add_argument("--run-cbmc", action="store_true")

    parser.add_argument("--proof-timeout", type=int, default=300)
    parser.add_argument("--stats-timeout", type=int, default=300)

    parser.add_argument("--fresh", action="store_true")
    parser.add_argument("--output", type=str, default="cbmc_metrics.csv")
    parser.add_argument("--proof-id", type=str)

    parser.add_argument("--skip-proof", action="append", default=[])
    parser.add_argument("--skip-attempted", action="store_true")
    parser.add_argument("--mark-attempted", action="store_true")
    parser.add_argument(
    "--skip-proof-file",
    action="append",
    default=[],
    help="Path to file with proofs to skip (one per line; supports # comments). Can be repeated.",
    )


    args = parser.parse_args()

    workspace = Path(args.workspace).expanduser().resolve()
    workspace.mkdir(parents=True, exist_ok=True)

    output_path = Path(args.output).expanduser().resolve()
    output_path.parent.mkdir(parents=True, exist_ok=True)

    if args.fresh and output_path.exists():
        output_path.unlink()

    completed = set() if args.fresh else load_completed_keys(output_path)

    repos = args.repo or REPOS

    skip_proofs = set(SKIP_PROOFS)

    # from repeated --skip-proof flags
    skip_proofs.update([s.strip().rstrip("/") for s in (args.skip_proof or []) if s and s.strip()])

    # from one or more skip files
    for fp in (args.skip_proof_file or []):
        if not fp or not fp.strip():
            continue
        skip_proofs.update(load_skip_list(Path(fp).expanduser().resolve()))


    repo_dir_override = Path(args.repo_dir).expanduser().resolve() if args.repo_dir else None

    for repo in repos:
        print(f"\n[INFO] Processing repo: {repo}")
        collect_metrics_for_repo(
            repo=repo,
            workspace=workspace,
            repo_dir_override=repo_dir_override,
            skip_clone=args.skip_clone,
            run_cbmc_flag=args.run_cbmc,
            proof_filter=args.proof_id,
            output_path=output_path,
            timeout_seconds=args.proof_timeout,
            stats_timeout_seconds=args.stats_timeout,
            completed_keys=completed,
            skip_proofs=skip_proofs,
            skip_attempted=args.skip_attempted,
            mark_attempted=args.mark_attempted,
        )

    print(f"[INFO] Finished. {output_path}")


if __name__ == "__main__":
    main()
