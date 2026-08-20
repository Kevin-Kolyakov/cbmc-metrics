# Exploration: Classifying Assertions and Assumptions in CBMC Proofs

This document explores how assertions and assumptions in the CBMC proofs can be
classified, and records how far the existing scripts in this repo already go.

## 1. What is already explored in this repo

### Assumptions

All three collectors count assumptions the same way — a single regex over the
C files in scope, summed into one column `num_preconditions`:

```python
pattern = re.compile(r"__CPROVER_precondition|CBMC_PRECONDITION|__CPROVER_assume")
```

- `collect_cbmc_metrics.py` → `count_preconditions_in_files()` (line 248)
- `collect_cbmc_metrics_autoup.py` → `count_preconditions()` (line 159)
- `collect_cbmc_mettrics_hand.py` → `count_preconditions_in_files()` (line 191)

Limitations of the current approach:

- **Everything is one bucket.** A harness precondition, an assumption buried in
  a stub/model file, and a `CBMC_PRECONDITION` contract macro all count as the
  same thing.
- **No intent captured.** A pointer-validity assumption, a size bound, and an
  enum-range restriction are indistinguishable.
- **Text match only.** Occurrences in comments or dead `#if 0` blocks count too.

### Assertions

Assertions are **not counted anywhere**. The only related metric is
`num_errors`, which counts *failed* properties:

- `collect_cbmc_metrics.py` / `collect_cbmc_mettrics_hand.py`: length of the
  `results.false` list in `viewer-result.json`.
- `collect_cbmc_metrics_autoup.py`: `parse_property_xml_num_errors()` counts
  `<property status="FAILURE">` elements in `build/reports/property.xml`.

Notably, **neither parser reads the property class** even though both files
carry it — so a failing user `assert` and a failing automatic overflow check
are currently indistinguishable, and passing properties are ignored entirely.

### What the collected CSVs show today

From the per-repo CSVs on `main` (general collector, hand-written proofs):

| CSV  | Repo                          | Proofs | Mean preconds | Max | Zero-precond proofs | Proofs w/ errors |
|------|-------------------------------|--------|---------------|-----|---------------------|------------------|
| out  | aws/s2n-tls                   | 139    | 1.2           | 7   | 46                  | 0                |
| out2 | awslabs/aws-c-common          | 147    | 2.0           | 9   | 27                  | 42               |
| out3 | aws/ota-for-aws-iot-...       | 121    | 1.1           | 7   | 57                  | 0                |
| out4 | aws/aws-encryption-sdk-c      | 29     | 3.9           | 19  | 5                   | 0                |
| out5 | aws-stm32-ml-at-edge-...      | 231    | 1.5           | 7   | 78                  | n/a (missing)    |
| out6 | FreeRTOS-Cellular-Interface   | 46     | 0.4           | 4   | 36                  | 2                |

The large "zero preconditions" counts are themselves a classification signal:
many harnesses either express constraints another way (e.g. bounded types,
allocation helpers) or keep their assumptions in shared stub files that were
not in the counted scope.

## 2. Two complementary classification axes

There are two independent sources of truth, and they classify different things:

### Axis A — source-level classification (what the harness author wrote)

Scan the C files of a proof and classify each occurrence of an
assumption/assertion primitive along two dimensions:

**By construct**

| Category        | Matched primitives                                          |
|-----------------|-------------------------------------------------------------|
| `assume`        | `__CPROVER_assume(...)`                                      |
| `precondition`  | `__CPROVER_precondition(...)`, `CBMC_PRECONDITION(...)`      |
| `assert`        | `assert(...)` (from `<assert.h>`)                            |
| `cprover_assert`| `__CPROVER_assert(...)`                                      |
| `postcondition` | `__CPROVER_postcondition(...)`, `POSTCONDITION(...)`, `__CPROVER_ensures(...)` |

**By file role** — where the statement lives changes its meaning:

| Role      | Detection heuristic                                              |
|-----------|------------------------------------------------------------------|
| `harness` | file name ends in `_harness.c` or matches the proof/entry name   |
| `stub`    | file name contains `stub`, `model`, `mock`, or lives under a shared `stubs/`, `sources/`, `helpers/` dir |
| `source`  | anything else in scope (project source pulled into the proof)    |

An assumption in a harness is a *specification decision* (input constraint);
the same assumption in a stub is a *modeling decision*; an `assert` in a
harness is the *proof obligation itself*.

**By intent (heuristic, on the argument text)** — priority-ordered:

1. `pointer-validity` — mentions `__CPROVER_r_ok` / `__CPROVER_w_ok` /
   `__CPROVER_rw_ok` / `IMPLIES` / `_is_valid` / `allocated`
2. `null-check` — compares against `NULL`
3. `bounds` — relational operator with `size`/`len`/`length`/`capacity`/`MAX`/
   a numeric literal
4. `equality/range` — `==` membership chains (typical enum restriction)
5. `other`

Intent classification is inherently fuzzy; it should be reported as a
distribution, not treated as exact.

### Axis B — result-level classification (what CBMC actually checked)

Every property CBMC reports has an ID of the form
`<function>.<property_class>.<n>` (e.g. `s2n_stuffer_read.pointer_dereference.5`,
`harness.assertion.1`), and `property.xml` additionally carries an explicit
`class` attribute. This gives an exact, tool-defined classification with no
heuristics:

| Class group        | Property classes                                                        | Meaning                          |
|--------------------|-------------------------------------------------------------------------|----------------------------------|
| `user-assertion`   | `assertion`                                                             | `assert` written by a human      |
| `contract`         | `precondition`, `precondition_instance`, `postcondition`                | contract instrumentation         |
| `memory-safety`    | `pointer_dereference`, `pointer_arithmetic`, `pointer`, `array_bounds`, `memory-leak`, `pointer_primitives` | automatic memory checks |
| `arithmetic`       | `overflow`, `division-by-zero`, `NaN`, `bit_count`, `shift`             | automatic arithmetic checks      |
| `unwinding`        | `unwind`                                                                | loop-unwinding assertions        |
| `stdlib-model`     | properties emitted inside `memcpy`, `memset`, `strlen`, ... functions   | checks in CBMC's library models  |
| `other`            | anything unrecognized                                                   | —                                |

Both `viewer-result.json` (`results.true` / `results.false` lists of property
IDs) and `build/reports/property.xml` (`<property name=... class=... status=...>`)
contain what's needed — the repo's parsers already open both files and simply
discard this information today.

Cross-referencing the axes is the interesting part: e.g. "proofs whose only
checked properties are automatic checks" (no user assertion at all — the proof
is purely a memory-safety proof) vs. "proofs with functional `assert`s", or
"failures concentrated in `unwind` class" (bounds problem, not a code bug —
likely explains part of aws-c-common's 42 error rows).

## 3. Prototype

`classify_assertions.py` (added alongside this doc) implements both axes:

```
# Source-level, one proof dir:
python3 classify_assertions.py --proof-dir path/to/proofs/foo

# Scan a whole workspace / repo checkout, write CSV:
python3 classify_assertions.py --scan-root cbmc-metrics-workspace --output classified.csv
```

Per proof it emits:

- `assume_harness`, `assume_stub`, `assume_source` — assumptions by file role
- `precondition_macros` — `__CPROVER_precondition` / `CBMC_PRECONDITION` uses
- `assert_harness`, `assert_stub`, `assert_source`, `cprover_asserts`,
  `postconditions` — assertion-side counts
- `intent_*` — intent distribution over assumptions
- `props_<group>_pass` / `props_<group>_fail` — result-level counts per class
  group, when `viewer-result.json` or `property.xml` is present

The source-level totals (`assume_* + precondition_macros`) reproduce the
existing `num_preconditions` number, so results are comparable with the CSVs
already collected.

## 4. Suggested next steps

1. Run the prototype over the same workspaces that produced `out*.csv` and the
   AutoUP/hand datasets, and join on `repo,proof_id` (the same key
   `average_harness_metrics.py` uses) to extend the comparison of hand-written
   vs AutoUP harnesses: do generated harnesses assume more/less, and of what
   kind?
2. Fold the property-class breakdown into `num_errors`: report
   `errors_user_assertion` / `errors_memory_safety` / `errors_unwinding`
   separately — an unwinding failure and a real assertion failure mean very
   different things.
3. Harden the source scan (strip comments/preprocessor-disabled code before
   matching; the prototype already strips comments and strings).
4. If intent classification matters for the study, replace the regex intent
   heuristics with a clang-based AST pass over the assumption arguments.
