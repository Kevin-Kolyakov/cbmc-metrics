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
from typing import List, Optional, Dict, Any, Tuple


REPOS = [
    "aws/s2n-tls",
    #"aws/aws-lc", no proofs found
    "awslabs/aws-c-common",
    "aws/ota-for-aws-iot-embedded-sdk",
    "aws/aws-encryption-sdk-c",
    #"awslabs/LibMLKEM", no proofs found
    "aws-samples/aws-stm32-ml-at-edge-accelerator", 
    #"aws-samples/aws-iot-alexa-connected-home-demo", proof error
    #"aws-greengrass/aws-greengrass-sdk-lite", no makefile found
    #"awslabs/aws-verification-model-for-libcrypto", no proofs found
    #"lkk688/AWSIoTFreeRTOS", make failed
    #"eddelbuettel/pkg-aws-c-common", make failed
    #"FreeRTOS/FreeRTOS-Plus-TCP", no makefile
    #"wiznetindia/WizFi360_EVB_PICO_AWS_controlling_LED", make failed
    #"FreeRTOS/coreHTTP", # doesnt print properly?
    "FreeRTOS/FreeRTOS-Cellular-Interface",
    #"FreeRTOS/corePKCS11", # doesnt print properly?
    #"FreeRTOS/coreSNTP", # doesnt print properly?
    "1NCE-GmbH/blueprint-freertos",
    #"ambiot/amazon-freertos", #make failed
    #"TF-RMM/tf-rmm", # no proofs found
    #"thufv/Deagle", # no proofs found
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

    symex_steps: Optional[int] = None
    sat_vars: Optional[int] = None  # sometimes doesn't appear depending on the repo and proof
    sat_clauses: Optional[int] = None # sometimes doesn't appear depending on the repo and proof
    max_unwind: Optional[int] = None # doesn't appear if no unwindings

    runtime_seconds: Optional[float] = None
    total_coverage: Optional[float] = None
    target_coverage: Optional[float] = None
    num_errors: Optional[int] = None

    def to_row(self) -> Dict[str, Any]:
        return asdict(self)


def safe_read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        return ""


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

def find_proof_dirs(repo_root: Path) -> List[Path]:
    proof_dirs: List[Path] = []

    # finding cbmc/proofs directory
    for cbmc_dir in repo_root.rglob("cbmc"):
        proofs_root = cbmc_dir / "proofs"
        if proofs_root.is_dir():
            for sub in proofs_root.iterdir():
                if sub.is_dir() and list(sub.rglob("*.c")):
                    proof_dirs.append(sub)

    #trying to find proof directories
    for proofs_root in repo_root.rglob("proofs"):
        if not proofs_root.is_dir():
            continue
        for sub in proofs_root.iterdir():
            if not sub.is_dir():
                continue
            has_c = any(p.suffix in (".c", ".i") for p in sub.rglob("*.c"))
            has_log = any("cbmc" in p.name.lower() and p.suffix in (".log", ".txt") for p in sub.rglob("*"))
            if has_c or has_log:
                proof_dirs.append(sub)

    # duplicate handling
    uniq: List[Path] = []
    seen = set()
    for p in proof_dirs:
        rp = p.resolve()
        if rp not in seen:
            seen.add(rp)
            uniq.append(rp)
    return uniq

def count_lines_of_code(harness_files: List[Path]) -> int:
    loc = 0
    for f in harness_files:
        for line in safe_read_text(f).splitlines():
            stripped = line.strip()
            if not stripped or stripped.startswith("//") or stripped.startswith("/*"):
                continue
            loc += 1
    return loc


def count_preconditions_in_files(files: List[Path]) -> int:
    pattern = re.compile(r"__CPROVER_precondition|CBMC_PRECONDITION|__CPROVER_assume")
    count = 0
    for f in files:
        text = safe_read_text(f)
        count += len(pattern.findall(text))
    return count


def count_models_in_files(files: List[Path]) -> Tuple[int, int]:
    var_pattern = re.compile(r"\bnondet_[a-zA-Z0-9_]+\s*\(")
    func_decl_pattern = re.compile(r"\b[a-zA-Z_][a-zA-Z0-9_]*_stub\b|\b[a-zA-Z_][a-zA-Z0-9_]*_model\b")

    var_models = 0
    func_models = 0

    for f in files:
        text = safe_read_text(f)
        var_models += len(var_pattern.findall(text))
        func_models += len(func_decl_pattern.findall(text))

        if f.name.lower().endswith(("stubs.c", "models.c")):
            func_models += 1

    return var_models, func_models

def get_viewer_json_dir(proof_dir: Path) -> Optional[Path]:
    json_dir = proof_dir / "report" / "json"
    if json_dir.is_dir():
        return json_dir
    return None


def parse_viewer_result_json(json_dir: Path) -> Dict[str, Any]:
    result_path = json_dir / "viewer-result.json"
    if not result_path.is_file():
        return {}

    try:
        raw = json.loads(result_path.read_text(encoding="utf-8"))
    except Exception:
        return {}

    vr = raw.get("viewer-result", raw)
    stats: Dict[str, Any] = {}

    # errors
    results = vr.get("results", {})
    false_props = results.get("false") or []
    if isinstance(false_props, list):
        stats["num_errors"] = len(false_props)

    status_lines = vr.get("status") or []

    # SAT vars and clausses
    last_vars = last_clauses = None
    for line in status_lines:
        m = re.search(r"([0-9,]+)\s+variables,\s*([0-9,]+)\s+clauses", line)
        if m:
            last_vars, last_clauses = m.groups()
    if last_vars and last_clauses:
        stats["sat_vars"] = int(last_vars.replace(",", ""))
        stats["sat_clauses"] = int(last_clauses.replace(",", ""))

    # runtime
    for line in status_lines:
        m = re.search(r"Runtime decision procedure:\s*([0-9.]+)\s*s", line)
        if m:
            stats["runtime_seconds"] = float(m.group(1))
            break

    # symex steps
    for line in status_lines:
        m = re.search(r"size of program expression:\s*([0-9,]+)\s+steps", line)
        if m:
            stats["symex_steps"] = int(m.group(1).replace(",", ""))
            break

    max_unwind_found = False
    for line in status_lines:
        m = re.search(r"loop(?:ing)?\s*=\s*([0-9,]+)", line)
        if m:
            stats["max_unwind"] = int(m.group(1).replace(",", ""))
            max_unwind_found = True
            break

    if not max_unwind_found:
        loop_path = json_dir / "viewer-loop.json"
        has_loops = None
        try:
            if loop_path.is_file():
                loop_raw = json.loads(loop_path.read_text(encoding="utf-8"))
                vl = loop_raw.get("viewer-loop", loop_raw)
                loops = vl.get("loops", {})
                if isinstance(loops, dict):
                    has_loops = bool(loops)
        except Exception:
            has_loops = None

        if has_loops is True:
            stats["max_unwind"] = 0
        elif has_loops is False or has_loops is None:
            stats["max_unwind"] = -1
            
    return stats


def parse_viewer_coverage_json(json_dir: Path) -> Dict[str, Any]:
    cov_path = json_dir / "viewer-coverage.json"
    if not cov_path.is_file():
        return {}

    try:
        raw = json.loads(cov_path.read_text(encoding="utf-8"))
    except Exception:
        return {}

    vc = raw.get("viewer-coverage", raw)
    overall = vc.get("overall_coverage") or {}
    stats: Dict[str, Any] = {}

    if "percentage" in overall:
        # convert to percentage
        pct = float(overall["percentage"]) * 100.0
        stats["total_coverage"] = pct
        stats["target_coverage"] = pct

    return stats


def run_cbmc_for_proof(proof_dir: Path) -> Tuple[Optional[float], str]:
    makefile = proof_dir / "Makefile"
    if not makefile.exists():
        print(f"[INFO] No Makefile in {proof_dir}, skipping CBMC run.")
        return None, ""

    env = os.environ.copy()

    print(f"[INFO] Running 'make' in {proof_dir}")
    start = time.time()
    result = subprocess.run(
        ["make"],
        cwd=str(proof_dir),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        env=env,
    )
    end = time.time()
    elapsed = end - start

    combined_output = result.stdout + "\n" + result.stderr

    if result.returncode != 0:
        print(
            f"[WARN] 'make' failed in {proof_dir} (exit {result.returncode}). "
            f"JSON reports may still contain useful info."
        )
    else:
        print(f"[INFO] 'make' in {proof_dir} finished in {elapsed:.2f}s")

    return elapsed, combined_output


def collect_metrics_for_proof(
    repo_name: str,
    proof_dir: Path,
    run_cbmc_flag: bool = False,
) -> ProofMetrics:
    proof_id = proof_dir.name
    metrics = ProofMetrics(
        repo=repo_name,
        proof_id=proof_id,
        proof_path=str(proof_dir),
    )

    # for LOC, preconditions, models, files
    all_c_files = list(proof_dir.rglob("*.c"))
    harness_files = [p for p in all_c_files if "harness" in p.name.lower()]
    if not harness_files:
        harness_files = all_c_files

    if harness_files:
        metrics.loc = count_lines_of_code(harness_files)

    if all_c_files:
        metrics.num_preconditions = count_preconditions_in_files(all_c_files)
        vm, fm = count_models_in_files(all_c_files)
        metrics.num_var_models = vm
        metrics.num_func_models = fm
        metrics.files_in_scope = len(all_c_files)

    elapsed: Optional[float] = None
    cbmc_output = ""
    if run_cbmc_flag:
        elapsed, cbmc_output = run_cbmc_for_proof(proof_dir)
        if elapsed is not None:
            metrics.runtime_seconds = round(elapsed, 3)

    json_dir = get_viewer_json_dir(proof_dir)
    if json_dir is not None:
        # Prefer cbmc-viewer JSON if available
        cov_stats = parse_viewer_coverage_json(json_dir)
        for k in ("total_coverage", "target_coverage"):
            v = cov_stats.get(k)
            if v is not None and getattr(metrics, k) is None:
                setattr(metrics, k, v)

        res_stats = parse_viewer_result_json(json_dir)
        for k, v in res_stats.items():
            # Do not overwrite wall-clock runtime from make
            if k == "runtime_seconds" and metrics.runtime_seconds is not None:
                continue
            if getattr(metrics, k) is None and v is not None:
                setattr(metrics, k, v)

    return metrics




def append_metrics_row(metrics: ProofMetrics, output_path: Path) -> None:
    row = metrics.to_row()
    file_exists = output_path.exists()
    write_header = (not file_exists) or (output_path.stat().st_size == 0)

    fieldnames = list(row.keys())

    with output_path.open("a", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        if write_header:
            writer.writeheader()
        writer.writerow(row)

def collect_metrics_for_repo(
    repo: str,
    workspace: Path,
    skip_clone: bool = False,
    run_cbmc_flag: bool = False,
    proof_filter: Optional[str] = None,
    output_path: Optional[Path] = None,
) -> List[ProofMetrics]:
    if skip_clone:
        owner, name = repo.split("/")
        repo_dir = workspace / name
        if not repo_dir.exists():
            raise FileNotFoundError(f"Repo directory does not exist and --skip-clone is set: {repo_dir}")
    else:
        repo_dir = git_clone(repo, workspace, skip_if_exists=True)

    proof_dirs = find_proof_dirs(repo_dir)

    # for single proofs
    if proof_filter:
        proof_dirs = [pd for pd in proof_dirs if pd.name == proof_filter]

    if not proof_dirs:
        print(f"[WARN] No proof directories found in {repo_dir}")
        return []

    metrics_list: List[ProofMetrics] = []
    for pd in proof_dirs:
        try:
            pm = collect_metrics_for_proof(repo, pd, run_cbmc_flag=run_cbmc_flag)
            metrics_list.append(pm)
            if output_path is not None:
                append_metrics_row(pm, output_path)
        except Exception as e:
            print(f"[ERROR] Failed to collect metrics for {repo} / {pd}: {e}", file=sys.stderr)

    return metrics_list


def main() -> None:
    parser = argparse.ArgumentParser(description="Collect CBMC proof metrics from multiple repos.")
    parser.add_argument(
        "--workspace",
        type=str,
        default="cbmc-metrics-workspace",
        help="Directory where repos are cloned/located.",
    )
    parser.add_argument(
        "--output",
        type=str,
        default="cbmc_metrics.csv",
        help="Path to output CSV file.",
    )
    parser.add_argument(
        "--repo",
        type=str,
        action="append",
        help="Specific repo(s) in owner/name form. If omitted, use built-in default list.",
    )
    parser.add_argument(
        "--skip-clone",
        action="store_true",
        help="Do not clone; assume repos already exist under workspace by their repo name.",
    )
    parser.add_argument(
        "--run-cbmc",
        action="store_true",
        help="Run CBMC for each proof directory (requires make + cbmc installed).",
    )
    parser.add_argument(
        "--proof-id",
        type=str,
        help="If set, only collect metrics for proofs whose directory name matches this id.",
    )

    args = parser.parse_args()
    workspace = Path(args.workspace).resolve()
    workspace.mkdir(parents=True, exist_ok=True)

    output_path = Path(args.output).resolve()
    # make sure output directory exists
    output_path.parent.mkdir(parents=True, exist_ok=True)
    
    if output_path.exists():
        output_path.unlink()

    repos = args.repo or REPOS

    for repo in repos:
        print(f"\n[INFO] Processing repo: {repo}")
        collect_metrics_for_repo(
            repo,
            workspace,
            skip_clone=args.skip_clone,
            run_cbmc_flag=args.run_cbmc,
            proof_filter=args.proof_id,
            output_path=output_path,
        )

    print(f"[INFO] Finished. {output_path}")


if __name__ == "__main__":
    main()
