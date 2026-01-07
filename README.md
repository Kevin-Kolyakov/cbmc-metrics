## Collecting Metrics

Script to collect certain metrics from CBMC proofs across multiple repos.

# Example Usage

python3 collect_cbmc_metrics.py \
  --repo owner/example-cbmc-repo \
  --workspace cbmc-metrics-workspace \
  --output cbmc_metrics.csv \
  --run-cbmc \
  --proof-timeout 300


### Metric Status

| Field               | Status                          |
|---------------------|---------------------------------|
| `loc`               | Working                         |
| `files_in_scope`    | Working                         |
| `num_preconditions` | Working                         |
| `num_var_models`    | Working                         |
| `num_func_models`   | Working                         |
| `symex_steps`       | Working                         |
| `sat_vars`          | Sometimes missing per proof     |
| `sat_clauses`       | Sometimes missing per proof     |
| `max_unwind`        | Working                         |
| `runtime_seconds`   | Working                         |
| `total_coverage`    | Working                         |
| `target_coverage`   | Working                         |
| `num_errors`        | Working                         |
