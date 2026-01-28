#!/usr/bin/env python3

"""
Usage: python3 average_harnes_metrics.py first.csv second.csv
Usage Example: python3 average_harness_metrics.py Hand-aws.csv AutoUP-aws.csv 
"""


import argparse
import sys
from typing import List

import pandas as pd

DEFAULT_KEY_COLS = ["repo", "proof_id"]

NUMERIC_COLS = [
    "loc",
    "files_in_scope",
    "num_preconditions",
    "num_var_models",
    "num_func_models",
    "symex_steps",
    "sat_vars",
    "sat_clauses",
    "max_unwind",
    "runtime_seconds",
    "total_coverage",
    "target_coverage",
    "num_errors",
]


def die(msg: str) -> None:
    print(f"ERROR: {msg}", file=sys.stderr)
    sys.exit(2)


def parse_key_cols(key_arg: str | None) -> List[str]:
    if not key_arg:
        return DEFAULT_KEY_COLS
    cols = [c.strip() for c in key_arg.split(",") if c.strip()]
    return cols or DEFAULT_KEY_COLS


def read_csv(path: str, key_cols: List[str]) -> pd.DataFrame:
    df = pd.read_csv(path)

    for k in key_cols:
        if k not in df.columns:
            die(f"{path}: missing key column '{k}'. Available columns: {list(df.columns)}")

    for c in NUMERIC_COLS:
        if c in df.columns:
            df[c] = pd.to_numeric(df[c], errors="coerce")

    for k in key_cols:
        if df[k].dtype == object:
            df[k] = df[k].astype(str).str.strip()

    return df


def collapse_per_proof(df: pd.DataFrame, key_cols: List[str]) -> pd.DataFrame:
    numeric_present = [c for c in NUMERIC_COLS if c in df.columns]
    if not numeric_present:
        return df[key_cols].drop_duplicates().copy()
    return df.groupby(key_cols, as_index=False).agg({c: "mean" for c in numeric_present})


def shared_keys(df1: pd.DataFrame, df2: pd.DataFrame, key_cols: List[str]) -> pd.DataFrame:
    return (
        df1[key_cols].drop_duplicates()
        .merge(df2[key_cols].drop_duplicates(), on=key_cols, how="inner")
    )


def filter_to_shared(df: pd.DataFrame, shared: pd.DataFrame, key_cols: List[str]) -> pd.DataFrame:
    return df.merge(shared, on=key_cols, how="inner")


def averages(df: pd.DataFrame, label: str) -> pd.DataFrame:
    cols = [c for c in NUMERIC_COLS if c in df.columns]
    if not cols:
        return pd.DataFrame(columns=[label])
    out = df[cols].mean(numeric_only=True).to_frame(name=label)
    out.index.name = "metric"
    return out


def safe_label(path: str) -> str:
    s = str(path).strip()
    s = s.replace("\n", " ").replace("\r", " ")
    s = s.replace(" ", "_")
    return s


def main(path_a: str, path_b: str, key_arg: str | None) -> None:
    key_cols = parse_key_cols(key_arg)

    df_a = collapse_per_proof(read_csv(path_a, key_cols), key_cols)
    df_b = collapse_per_proof(read_csv(path_b, key_cols), key_cols)

    shared = shared_keys(df_a, df_b, key_cols)
    if len(shared) == 0:
        die("No shared proofs found with the chosen key. Try a looser key (e.g., repo,proof_id).")

    a_shared = filter_to_shared(df_a, shared, key_cols)
    b_shared = filter_to_shared(df_b, shared, key_cols)

    label_a = f"avg({safe_label(path_a)})"
    label_b = f"avg({safe_label(path_b)})"

    summary = averages(a_shared, label_a).join(averages(b_shared, label_b), how="outer")
    summary[f"delta({safe_label(path_b)}-{safe_label(path_a)})"] = summary[label_b] - summary[label_a]
    summary = summary.sort_index()

    pd.set_option("display.max_rows", 200)
    pd.set_option("display.width", 160)
    print(summary.to_string(float_format=lambda x: f"{x:.6g}"))


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("fileA")
    ap.add_argument("fileB")
    ap.add_argument("--key", default=None)
    args = ap.parse_args()
    main(args.fileA, args.fileB, args.key)