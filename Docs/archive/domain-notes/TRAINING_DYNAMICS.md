# Training Dynamics Toolkit

This toolkit measures stepwise training behaviour without claiming mechanism.

## What it does

- compares baseline vs LILA logs
- plots loss and its derivative
- scans per-step deltas with the Δ-cone analyzer
- optionally encodes checkpoints as prime-exponent summaries

## One-command path

```bash
./scripts/run_all.sh
```

Outputs:

- `runs_compare/training_dynamics.png` (generated runtime plot, not a versioned
  docs preview)
- `runs_compare/delta_cone_rank.csv`

## Expected reading

Typical comparison signal:

- baseline transitions later or more sharply
- LILA transitions earlier or with a broader stabilization window
- read the analyzer as stability/regime-change tooling, not a safety proof

## Diagram

`Docs/TRAINING_DYNAMICS.puml` now shows the bridge in DASHI terms first:
`ExecutionContract`, `ExecutionContractReceipt`, `AdmissibleStep`,
`LilaDashiBridge`, `TraceRow`, and the projected `Delta` view.
`Docs/TRAINING_DYNAMICS.svg` is the rendered preview.

## Notes

- Adjust `FEATURES` and `ARROW` if your logs use different column names.
- `scripts/run_compare.sh` accepts `BASE_CMD`, `LILA_CMD`, and `STEPS`
  overrides so you do not need to edit the script for a local repo layout.
