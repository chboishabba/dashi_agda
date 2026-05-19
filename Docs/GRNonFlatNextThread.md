# GR Non-Flat Next Thread

Date: `2026-05-13`
Owner: `Worker 6 documentation/audit sidecar`
Status: `request-only; non-promoting`

This note records the next admissible discrete GR thread after the current flat
Minkowski/DET, CRT/J diagnostic, Schwarzschild candidate, continuum request, and
W4 matter/stress-energy interface surfaces. It is documentation only. It does
not close W4, G6, GR, Schwarzschild, continuum, or GR/QFT.

## Formal Model

- O: docs audit worker for the GR next live thread.
- R: preserve the current fail-closed state while recording the proposed
  discrete Riemann/Ricci/Einstein path.
- C: docs only; no Agda edits.
- S: W4 is not formally closed, G6 is not closed, and non-flat GR remains
  candidate/request-only unless a later worker lands imported typechecked
  receipts.
- L: this file is a short handoff; `Docs/CurrentGateStatus.md` is the read-first
  status layer.
- P: promote only from inhabited theorem, receipt, or token surfaces.
- G: no closure labels without a bounded Agda validation receipt for the exact
  imported theorem/receipt.
- F: blockers below are hard blockers, not prose TODOs.

## Discrete GR Path

1. Carrier-internal non-flat connection:
   `killMissingCarrierInternalNonFlatConnectionFromCRT` remains the first kill
   condition. CRT/J period and scalar diagnostics are not connection data.
2. Discrete Riemann/curvature:
   define curvature as a bracket/parallel-transport defect over the selected
   finite-r carrier, with explicit connection coefficients or shift law.
3. Bianchi identity:
   prove the finite-r Jacobi-to-Bianchi bridge, including
   `missingFiniteRJacobiWitness`, `missingCurvatureAsBracketDefect`,
   `missingCovariantExteriorDerivativeOrCyclicSum`,
   `missingJacobiToBianchiBridge`, and `missingFiniteRBianchiLaw`.
4. Ricci contraction:
   provide metric contraction from curvature to Ricci, scalar trace, and the
   curvature-to-Ricci/Einstein contraction boundary.
5. Discrete Einstein tensor:
   define the tensor law only after curvature, Ricci, scalar trace, metric
   compatibility, and contraction laws are available.
6. Sourced Einstein equation:
   consume `EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt`.
   Until that receipt exists, `matterFieldFromW4`, `stressEnergyTensorFromW4`,
   and `G_mu_nu = 8pi T_mu_nu` are obligation shapes only.
7. `G_N` diagnostic:
   `G_N` may be recorded only as a normalization/weak-field diagnostic target.
   It cannot be promoted without physical-unit authority, W4 mass source,
   weak-field Newtonian-potential law, and dimensional-preservation evidence.
8. Error bounds and continuum:
   metric error bound, connection error bound, Einstein tensor continuity, and
   W2 rate/bridge resolution remain required before continuum scaling language.

## Exact Blockers

The current blocker list is:

- `missingCarrierInternalNonFlatConnectionFromCRT`
- `missingCurvatureToRicciContraction`
- `missingFiniteRBianchiWitness`
- `missingDiscreteEinsteinTensorLaw`
- `missingW4MatterStressEnergyInterfaceReceipt`
- `missingMetricErrorBound`
- `missingConnectionErrorBound`
- `missingWeakFieldNewtonianPotential`
- `missingW4MassSource`
- `missingSchwarzschildMetricMatch`
- `missingEinsteinTensorContinuity`
- `missingW2BridgeOrObstructionResolution`

Unsupported claims remain unsupported: non-flat GR promotion, finite-r Bianchi
closure, W4 matter-coupling closure, metric/connection continuum error closure,
Schwarzschild derivation, G6 commutativity from a GR candidate, and GR/QFT
promotion.

## Timeout Rule

All validation must be bounded. Use `timeout 30s`; do not run uncapped Agda:

```bash
timeout 30s agda -i . PATH/TO/Module.agda
```

For this docs-only lane, run:

```bash
git diff --check -- Docs/CurrentGateStatus.md Docs/GRNonFlatNextThread.md
```
