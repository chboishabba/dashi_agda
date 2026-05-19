# LILA / DASHI Bridge

Resolved thread metadata:

- title: `LILA-Trinity R&D Discussion`
- online thread ID: `69d30a80-6ed8-839b-a712-c751b517246d`
- canonical thread ID: `9f1b35187081584dfd0d43a51f0e7931bde2d6c3`
- source used for resolution: DB after web ingestion

## Bridge Reading

The thread settles on a specific interpretation:

- LILA is the execution system.
- DASHI is the formal lens that constrains and validates that execution.
- The bridge is not an equality claim.
- The bridge is a contract surface: execution traces are judged by admissibility.

## Normalized Contract Surface

The bridge is best read through the existing execution contract tuple:

- organization: the LILA model, training loop, and dataset context
- requirement: loss minimization and coherent output production
- code/operator: forward pass, weight update, memory update
- state: weights, activations, memory state, logits
- lattice: state order plus projected-delta and MDL structure

## Structured Extract

The normalized bridge section from the thread reduces to:

1. LILA should be interpreted inside DASHI rather than identified with it.
2. LILA contributes the evolving execution state.
3. DASHI contributes the admissibility geometry and receipt layer.
4. The core invariant is trace admissibility under projected deltas.
5. The next useful step is a concrete bridge module and a concrete trace instantiation.

## Current Repo Consequence

- keep the bridge language execution-side on the LILA side
- keep the admissibility / receipt language on the DASHI side
- use the existing `ExecutionContract` and `ExecutionContractLaws` modules as the formal seam
- use `scripts/delta_cone_lila.py` for the trace-side Δ-cone scan
- use `scripts/checkpoint_prime_vectors.py` for the prime-exponent checkpoint lift
- use `DASHI/Physics/Closure/LilaTraceFamily.agda` as the minimal row-to-receipt schema
- use `scripts/run_compare.sh` and `scripts/plot_training_dynamics.py` as the
  minimal credibility/evaluation harness for baseline-vs-LILA comparisons
- use `scripts/run_all.sh` as the one-command runner for the compare, plot,
  and delta-cone path
- keep the short usage page in `Docs/TRAINING_DYNAMICS.md` and the PlantUML
  source in `Docs/TRAINING_DYNAMICS.puml` as the repo-facing quickstart
