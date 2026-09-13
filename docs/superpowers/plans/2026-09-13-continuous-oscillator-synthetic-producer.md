# Continuous Oscillator Synthetic Producer Implementation Plan

Date: 2026-09-13
Branch: `agent/continuous-oscillator-synthetic-producer`

## Execution order

1. RED: add focused pytest contract for the producer CLI/artifacts and deterministic 3/6/9 conditions. Verify it fails because the producer does not exist.
2. GREEN: add the smallest deterministic Python producer satisfying that contract. Verify focused pytest passes.
3. RED: extend pytest with numerical invariants: fixed frequency support, decreasing fit loss, finite readouts, deterministic summaries, and fail-closed promotion flags. Verify any new assertion fails before implementation.
4. GREEN: add only the numerical learning/readout implementation required by those assertions.
5. REFACTOR: keep objective/readout helpers small and deterministic; rerun focused tests.
6. RED: add receipt-surface static test if needed to require the Agda receipt/promotion guards before creating it.
7. GREEN: add `DASHI/Cognition/PNF/ContinuousOscillatorSyntheticReceipt.agda` and narrow aggregate import.
8. Update `Docs/roadmaps/SimulatorRoadmap.md` only after numerical tests are green.
9. Verification: focused pytest; syntax compile for Python; narrow Agda compile if a compiler/CI receipt exists; diff/status checks; workflow runs.

## Files

Create:

- `tests/test_continuous_oscillator_synthetic.py`
- `scripts/run_continuous_oscillator_synthetic.py`
- `DASHI/Cognition/PNF/ContinuousOscillatorSyntheticReceipt.agda`

Modify narrowly:

- `DASHI/Cognition/PNF/PNFIRLearningEverything.agda`
- `Docs/roadmaps/SimulatorRoadmap.md`

## Default numerical contract

- fixed target frequencies: three frequencies shared by all conditions;
- N in `{3, 6, 9}`;
- deterministic seed set, default at least three seeds;
- amplitudes/phases initialized from seeded RNG;
- gradient descent only on amplitudes/phases;
- same-frequency phase regularization;
- small amplitude L2 regularization;
- finite maximum steps and convergence tolerance;
- no requirement that N=9 numerically dominates N=6 or N=3.

## Required output schema

Summary JSON contains:

- diagnostic/status/schema version;
- target definition;
- default seeds;
- results keyed by `(N, seed)`;
- comparison summary by N;
- promotion boundary flags;
- output paths.

Trajectory CSV contains selected optimization snapshots for each `(N, seed)`.

Comparison CSV contains one final row per `(N, seed)`.

Markdown report renders the target, all declared runs, readouts, and fail-closed boundaries.

## Verification boundary

Do not claim Agda green without an actual compiler/workflow receipt. Python tests can be verified locally by materializing the changed Python files into the execution container if repository checkout/network access is unavailable.
