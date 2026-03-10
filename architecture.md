# Architecture Notes for DashI Closure Path

## Current canonical stack
- Constraint layer: `CanonicalStageC` orchestrates canonical gauge, algebraic, and
  wave modules, exporting `CanonicalStageCTheoremBundle` and `CanonicalStageCSummaryBundle`.
- Recovery layer: known-limits modules now include propagation, geometry transport,
  local coherence, extended recovery, the new local causal-effective propagation,
  and the local causal-geometry coherence theorem, culminating in
  `KnownLimitsRecoveredDynamicsTheorem` anchored by `CanonicalDynamicsLawTheorem`.
- Bridge layer: Stage C now re-exports `KnownLimitsMatterGaugeTheorem`, with existing
  GR and QFT bridge theorems depending on it.

## Remaining architecture work
1. Formalize the full gauge/matter recovery theorem so the bridge no longer rests
   on prototype assumptions.
2. Extend the GR and QFT bridge records with this strengthened recovery as a
   prerequisite milestone.
3. Document this path in `PhysicsClosureSummary.agda` and `PhysicsClosureValidationSummary.agda`.

## Signals to watch
- `status.json` should flip `milestones_remaining` to 0 once the bridge and
  dynamics pillars are recorded as canonical exports.
- `COMPACTIFIED_CONTEXT.md` should summarize each fixed theorem surface.
