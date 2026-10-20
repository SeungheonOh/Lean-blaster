# Pass 2 differential fuzzing — running findings log

Harness: `gen.py` (random props; `ground` = closed props, oracle `#eval decide P`; `quant` = ∀-props, oracle =
bounded `#eval decide (∀ x ∈ vals, …)`), `run.sh` (parallel `lake env lean --json`), `check.py` (compare).
Each `#blaster` uses `(timeout: 5) (gen-cex: 0)`.

## Volume / verdicts (cumulative)

- r0 (smoke): 20 ground + 20 quant; all verdicts agree with oracle.

## Confirmed NEW unsound findings

(none yet)

## Duplicates of known (REPORT.md) root causes

## Completeness bugs / crash classes
