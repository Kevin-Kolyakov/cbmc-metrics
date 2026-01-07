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


REPOS = [
    "aws/s2n-tls",
    # "aws/aws-lc", no proofs found
    "awslabs/aws-c-common",
    "aws/ota-for-aws-iot-embedded-sdk",
    "aws/aws-encryption-sdk-c",
    # "awslabs/LibMLKEM", no proofs found
    "aws-samples/aws-stm32-ml-at-edge-accelerator",
    # "aws-samples/aws-iot-alexa-connected-home-demo", proof error
    # "aws-greengrass/aws-greengrass-sdk-lite", no makefile found
    # "awslabs/aws-verification-model-for-libcrypto", no proofs found
    # "lkk688/AWSIoTFreeRTOS", make failed
    # "eddelbuettel/pkg-aws-c-common", make failed
    # "FreeRTOS/FreeRTOS-Plus-TCP", no makefile
    # "wiznetindia/WizFi360_EVB_PICO_AWS_controlling_LED", make failed
    # "FreeRTOS/coreHTTP", # doesnt print properly?
    "FreeRTOS/FreeRTOS-Cellular-Interface",
    # "FreeRTOS/corePKCS11", # doesnt print properly?
    # "FreeRTOS/coreSNTP", # doesnt print properly?
    "1NCE-GmbH/blueprint-freertos",
    # "ambiot/amazon-freertos", #make failed
    # "TF-RMM/tf-rmm", # no proofs found
    # "thufv/Deagle", # no proofs found
]

# Hard-coded skip list by proof directory name (proof_id).
# Add whatever you want here.
SKIP_PROOFS: Set[str] = {
    "Cellular_ATRemoveLeadingWhiteSpaces",
    "Cellular_ATRemoveAllDoubleQuote",
    "Cellular_ATRemoveAllWhiteSpaces",
    "Cellular_ATcheckErrorCode",
    "Cellular_ATRemoveTrailingWhiteSpaces",
    "Cellular_ATStrDup",
    "Cellular_ATHexStrToHex",
    "_Cellular_PdnEventCallback",
    "Cellular_ATRemoveOutermostDoubleQuote",
    "Cellular_CommonCreateSocket",
    "Cellular_CommonGetNetworkTime",
    "_Cellular_ComputeSignalBars",
    "Cellular_CommonSetEidrxSettings",
    "Cellular_CommonSetEidrxSettings",
    "Cellular_ATRemovePrefix",
    "s2n_stuffer_private_key_from_pem",
    "aws_array_list_push_front",
    "aws_hash_table_remove",
    "aws_priority_queue_s_sift_down",
    "aws_array_list_erase",
    "aws_string_eq_byte_cursor",
    "aws_hash_table_find",
    "aws_priority_queue_push",
    "aws_hash_iter_done",
    "aws_byte_cursor_read",
    "aws_priority_queue_s_sift_either",
    "aws_byte_cursor_compare_lookup",
    "aws_hash_table_put",
    "aws_array_list_push_back",
    "aws_priority_queue_push_ref",
    "aws_byte_cursor_read_be64",
    "aws_hash_table_move",
    "aws_hash_table_create",
    "aws_priority_queue_s_remove_node",
    "aws_cryptosdk_keyring_trace_record_init_clone",
    "aws_cryptosdk_keyring_trace_record_clean_up",
    "aws_cryptosdk_private_commitment_eq",
    "aws_cryptosdk_sig_get_pubkey",
    "sign_header",
    "aws_cryptosdk_priv_algorithm_allowed_for_encrypt",
    "aws_cryptosdk_aes_gcm_encrypt",
    "aws_cryptosdk_priv_hdr_parse_iv_len",
    "aws_cryptosdk_priv_hdr_parse_reserved",
    "aws_cryptosdk_enc_ctx_serialize",
    "aws_cryptosdk_rsa_encrypt",
    "aws_cryptosdk_default_cmm_set_alg_id",
    "aws_cryptosdk_keyring_trace_copy_all",
    "aws_cryptosdk_edk_list_clean_up",
    "aws_cryptosdk_sig_sign_finish",
    "aws_cryptosdk_priv_hdr_parse_header_version",
    "aws_cryptosdk_keyring_trace_add_record",
    "aws_cryptosdk_enc_ctx_clone",
    "aws_cryptosdk_priv_hdr_parse_auth_tag",
    "aws_cryptosdk_keyring_trace_eq",
    "aws_cryptosdk_hdr_size",   
    "aws_cryptosdk_cmm_release",
    "aws_cryptosdk_keyring_trace_add_record_buf",
    "aws_cryptosdk_aes_gcm_decrypt",
    "aws_cryptosdk_sig_sign_start_keygen",
    "aws_cryptosdk_md_finish",
    "aws_cryptosdk_priv_hdr_parse_edks",
    "aws_cryptosdk_priv_hdr_parse_message_type",
    "aws_cryptosdk_cmm_generate_enc_materials",
    "aws_cryptosdk_enc_ctx_clear",
    "aws_cryptosdk_sig_update",
    
}

# Marker file name used to remember a proof was already attempted.
ATTEMPT_MARKER = ".cbmc_attempted"


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
    sat_vars: Optional[int] = None
    sat_clauses: Optional[int] = None
    max_unwind: Optional[int] = None

    runtime_seconds: Optional[float] = None
    total_coverage: Optional[float] = None
    target_coverage: Optional[float] = None
    num_errors: Optional[int] = None

    def to_row(self) -> Dict[str, Any]:
        return asdict(self)


def _as_text(x: Union[str, bytes, None]) -> str:
    if x is None:
        return ""
    if isinstance(x, bytes):
        return x.decode("utf-8", errors="replace")
    return x


def load_completed_keys(csv_path: Path) -> Set[Tuple[str, str]]:
    """
    Read an existing CSV and return completed proof keys as (repo, proof_id).
    Used for resume mode.
    """
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

    # trying to find proof directories
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

    # SAT vars and clauses
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
        pct = float(overall["percentage"]) * 100.0
        stats["total_coverage"] = pct
        stats["target_coverage"] = pct

    return stats


def run_cbmc_for_proof(proof_dir: Path, timeout_seconds: int) -> Tuple[Optional[float], str, bool]:
    """
    Returns (elapsed_seconds, combined_output, timed_out)
    """
    makefile = proof_dir / "Makefile"
    if not makefile.exists():
        print(f"[INFO] No Makefile in {proof_dir}, skipping CBMC run.")
        return None, "", False

    env = os.environ.copy()

    print(f"[INFO] Running 'make' in {proof_dir} (timeout={timeout_seconds}s)")
    start = time.time()
    try:
        result = subprocess.run(
            ["make"],
            cwd=str(proof_dir),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,  # stdout/stderr become str in most cases
            env=env,
            timeout=timeout_seconds,
        )
        elapsed = time.time() - start
        combined_output = _as_text(result.stdout) + "\n" + _as_text(result.stderr)

        if result.returncode != 0:
            print(
                f"[WARN] 'make' failed in {proof_dir} (exit {result.returncode}). "
                f"JSON reports may still contain useful info."
            )
        else:
            print(f"[INFO] 'make' in {proof_dir} finished in {elapsed:.2f}s")

        return elapsed, combined_output, False

    except subprocess.TimeoutExpired as e:
        elapsed = time.time() - start
        out = _as_text(e.stdout) + "\n" + _as_text(e.stderr)
        print(f"[WARN] Timeout after {timeout_seconds}s; skipping proof: {proof_dir}")
        return elapsed, out, True


def collect_metrics_for_proof(
    repo_name: str,
    proof_dir: Path,
    run_cbmc_flag: bool = False,
    timeout_seconds: int = 30,
) -> Optional[ProofMetrics]:
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

    if run_cbmc_flag:
        elapsed, _cbmc_output, timed_out = run_cbmc_for_proof(proof_dir, timeout_seconds)
        if timed_out:
            return None  # skip this proof entirely
        if elapsed is not None:
            metrics.runtime_seconds = round(elapsed, 3)

    json_dir = get_viewer_json_dir(proof_dir)
    if json_dir is not None:
        cov_stats = parse_viewer_coverage_json(json_dir)
        for k in ("total_coverage", "target_coverage"):
            v = cov_stats.get(k)
            if v is not None and getattr(metrics, k) is None:
                setattr(metrics, k, v)

        res_stats = parse_viewer_result_json(json_dir)
        for k, v in res_stats.items():
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
    timeout_seconds: int = 30,
    completed_keys: Optional[Set[Tuple[str, str]]] = None,
    skip_proofs: Optional[Set[str]] = None,
    skip_attempted: bool = False,
    mark_attempted: bool = False,
) -> List[ProofMetrics]:
    if skip_clone:
        owner, name = repo.split("/")
        repo_dir = workspace / name
        if not repo_dir.exists():
            raise FileNotFoundError(f"Repo directory does not exist and --skip-clone is set: {repo_dir}")
    else:
        repo_dir = git_clone(repo, workspace, skip_if_exists=True)

    proof_dirs = find_proof_dirs(repo_dir)

    if proof_filter:
        proof_dirs = [pd for pd in proof_dirs if pd.name == proof_filter]

    if not proof_dirs:
        print(f"[WARN] No proof directories found in {repo_dir}")
        return []

    completed_keys = completed_keys or set()
    skip_proofs = skip_proofs or set()

    metrics_list: List[ProofMetrics] = []
    for pd in proof_dirs:
        proof_id = pd.name

        # 1) Hard skip list
        if proof_id in skip_proofs:
            print(f"[INFO] Skipping proof (in skip list): {repo} / {proof_id}")
            continue

        # 2) Resume skip from CSV
        if (repo, proof_id) in completed_keys:
            print(f"[INFO] Skipping already-completed proof: {repo} / {proof_id}")
            continue

        # 3) Optional: skip proofs already attempted (marker file)
        marker_path = pd / ATTEMPT_MARKER
        if skip_attempted and marker_path.exists():
            print(f"[INFO] Skipping already-attempted proof (marker): {repo} / {proof_id}")
            continue

        try:
            pm = collect_metrics_for_proof(
                repo,
                pd,
                run_cbmc_flag=run_cbmc_flag,
                timeout_seconds=timeout_seconds,
            )

            # Mark attempted regardless of outcome (optional)
            if mark_attempted:
                try:
                    marker_path.write_text("attempted\n", encoding="utf-8")
                except Exception as e:
                    print(f"[WARN] Could not write attempt marker {marker_path}: {e}")

            if pm is None:
                continue  # timed out; skip

            metrics_list.append(pm)
            if output_path is not None:
                append_metrics_row(pm, output_path)
                completed_keys.add((repo, proof_id))  # skip within this run too

        except Exception as e:
            # Still mark attempted on exception if enabled
            if mark_attempted:
                try:
                    marker_path.write_text("attempted\n", encoding="utf-8")
                except Exception as e2:
                    print(f"[WARN] Could not write attempt marker {marker_path}: {e2}")

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
        "--proof-timeout",
        type=int,
        default=30,
        help="Skip a proof if its `make` run exceeds this many seconds (only with --run-cbmc).",
    )
    parser.add_argument(
        "--fresh",
        action="store_true",
        help="Start a fresh run by deleting the output CSV first (disables resume).",
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

    # NEW: skip controls
    parser.add_argument(
        "--skip-proof",
        action="append",
        default=[],
        help="Skip a proof by id (directory name). Can be provided multiple times.",
    )
    parser.add_argument(
        "--skip-attempted",
        action="store_true",
        help=f"Skip proofs that already contain the {ATTEMPT_MARKER} marker file.",
    )
    parser.add_argument(
        "--mark-attempted",
        action="store_true",
        help=f"Create {ATTEMPT_MARKER} in each proof dir after attempting it (even if it times out/fails).",
    )

    args = parser.parse_args()
    workspace = Path(args.workspace).resolve()
    workspace.mkdir(parents=True, exist_ok=True)

    output_path = Path(args.output).resolve()
    output_path.parent.mkdir(parents=True, exist_ok=True)

    if args.fresh and output_path.exists():
        output_path.unlink()

    completed = set() if args.fresh else load_completed_keys(output_path)

    repos = args.repo or REPOS

    # Combine hard-coded + CLI skip list
    skip_proofs = set(SKIP_PROOFS)
    skip_proofs.update([s.strip() for s in (args.skip_proof or []) if s and s.strip()])

    for repo in repos:
        print(f"\n[INFO] Processing repo: {repo}")
        collect_metrics_for_repo(
            repo,
            workspace,
            skip_clone=args.skip_clone,
            run_cbmc_flag=args.run_cbmc,
            proof_filter=args.proof_id,
            output_path=output_path,
            timeout_seconds=args.proof_timeout,
            completed_keys=completed,
            skip_proofs=skip_proofs,
            skip_attempted=args.skip_attempted,
            mark_attempted=args.mark_attempted,
        )

    print(f"[INFO] Finished. {output_path}")


if __name__ == "__main__":
    main()
