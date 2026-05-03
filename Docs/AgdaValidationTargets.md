# Agda Validation Targets

Purpose: record which Agda modules are safe for routine targeted validation and
which ones should be avoided in normal loops because they are known to be
runtime-heavy or aggregate too much of the closure surface at once.

## Safe Routine Targets

These are the preferred modules for focused validation while working on the
canonical closure spine:

- `DASHI/Geometry/CausalForcesLorentz31.agda`
- `DASHI/Geometry/Signature31FromIntrinsicShellForcing.agda`
- `DASHI/Physics/Signature31IntrinsicShiftInstance.agda`
- `DASHI/Physics/Signature31FromShiftOrbitProfile.agda`
- `DASHI/Physics/Closure/ContractionQuadraticToSignatureBridgeTheorem.agda`
- `DASHI/Physics/Closure/QuadraticToCliffordBridgeTheorem.agda`
- `DASHI/Physics/CliffordEvenLiftBridge.agda`
- `DASHI/Physics/Closure/CliffordToEvenWaveLiftBridgeTheorem.agda`
- `DASHI/Physics/Closure/CanonicalContractionToCliffordBridgeTheorem.agda`
- `DASHI/Physics/Closure/KnownLimitsQFTBridgeTheorem.agda`
- `DASHI/Physics/Closure/Canonical/LocalProgramBundle.agda`
- `DASHI/Physics/Closure/Canonical/Ladder.agda`
- `DASHI/Physics/Closure/PhysicsClosureSummary.agda`
- `DASHI/Algebra/TritTriTruthBridge.agda`
- `DASHI/Algebra/MoonshineBridge.agda`
- `DASHI/Algebra/StageQuotient.agda`
- `DASHI/Physics/TritCarrierBridge.agda`
- `DASHI/Physics/FascisticContractionInstance.agda`
- `DASHI/Physics/CRTPeriodJFixedBridge.agda`
- `DASHI/Physics/Closure/TemporalSheafProofObligations.agda`
- `DASHI/Physics/Closure/P0BlockerObligationIndex.agda`

Use these for routine theorem-edit loops and targeted bridge checks.

## Heavy / Certification-Only

These should not be part of normal rapid validation passes. They are closure
certification targets only:

- `DASHI/Physics/Closure/PhysicsClosureValidationSummary.agda`
- `DASHI/Everything.agda`
- `DASHI/Physics/Closure/ShiftContractObservableTransportPrimeCompatibilityProfileInstance.agda`
- `DASHI/Physics/Closure/ShiftObservableSignaturePressureConsumer.agda`
- `DASHI/Physics/DashiDynamicsShiftInstance.agda`
- `DASHI/Physics/Closure/CanonicalAbstractGaugeMatterInstance.agda`
- `DASHI/Physics/Closure/CanonicalGaugeMatterStrengtheningTheorem.agda`
- `DASHI/Physics/Closure/KnownLimitsFullMatterGaugeTheorem.agda`
- `DASHI/Physics/Closure/AtomicPhotonuclearContactGateTheorem.agda`
- `DASHI/Physics/Closure/CanonicalP2KeyScheduleBridgeObstruction.agda`
- `DASHI/Physics/Closure/CanonicalScheduleIndependentNaturalChargeNextIngredientGap.agda`

Reason:

- `PhysicsClosureValidationSummary.agda` is the known heavy aggregate closure
  summary and currently remains outside routine validation policy.
- `Everything.agda` is the authoritative top-level route, but bounded local
  checks currently time out because it eventually pulls the heavy validation
  summary path.
- The closure-recovery chain from
  `ShiftContractObservableTransportPrimeCompatibilityProfileInstance.agda`
  through `KnownLimitsFullMatterGaugeTheorem.agda` and
  `AtomicPhotonuclearContactGateTheorem.agda` repeatedly drags in the expensive
  shift/observable/canonical-gauge stack and should be treated as offline-only
  unless that exact lane is the subject of the current work.
- `CanonicalP2KeyScheduleBridgeObstruction.agda` is theorem-thin logically, but
  in practice still rebuilds the same natural-charge / canonical-gauge heavy
  cone as `CanonicalScheduleIndependentNaturalChargeNextIngredientGap.agda` and
  should be treated the same way.
- `CanonicalScheduleIndependentNaturalChargeNextIngredientGap.agda` appears to
  be logically live, but it currently pulls enough of the same heavy recovery
  stack that it should stay out of routine local validation.

## Natural-Charge Heavy-Lane Rule

The current natural-charge blocker family:

- `DASHI/Physics/Closure/CanonicalP2KeyScheduleBridgeObstruction.agda`
- `DASHI/Physics/Closure/CanonicalScheduleIndependentNaturalChargeNextIngredientGap.agda`

should not be run interactively without a very short cap.

Practical rule:

- if you absolutely probe one locally, use at most a `10s` timeout
- otherwise route it straight to `L2` / offline-only validation

Example:

- `timeout 10s agda -i . -l standard-library DASHI/Physics/Closure/CanonicalP2KeyScheduleBridgeObstruction.agda`
- `timeout 10s agda -i . -l standard-library DASHI/Physics/Closure/CanonicalScheduleIndependentNaturalChargeNextIngredientGap.agda`

## Bounded-Only Target

- `DASHI/Physics/Closure/CanonicalStageC.agda`

This module is not banned, but it is heavy enough that bounded runs can still
time out. Use it as a checkpoint module, not as the default inner-loop target.

## Certification-Only Rule

`L2` modules are never required for:

- branch classification
- roadmap state
- theorem promotion
- staging decisions in the normal interactive loop

`L2` modules are only required for:

- closure certification
- deliberate offline coherence checks
- decomposition work on the global closure cone

Interpretation rule:

- if an `L0` or `L1` target compiles, that is enough to classify the local lane
- if an `L2` target has not been rerun recently, that does not invalidate an
  `advanced` or `blocked` lane classification
- if an `L2` target fails, that is a closure-certification event, not an excuse
  to collapse branch status back into `unknown`

## Blocker Validation Matrix

| Blocker lane | Allowed validation level | Timeout / avoidance rule |
|---|---|---|
| `W1` MDL/CR carrier | `L0/L1` targeted seam modules | Check `CanonicalToNoncanonicalMdlRetargetFinalSeamObligation.agda` when the final seam boundary changes; avoid full closure aggregates. |
| `W2` natural / `p2` / convergence | `L2` for heavy natural-charge modules, `L0/L1` for thin helper modules | Check `NaturalP2ConvergencePromotionObligation.agda` for the promotion boundary; use at most a short timeout for heavier natural-charge modules, otherwise route offline. |
| `W3` empirical adequacy | `L0/L1` targeted empirical bridge modules | Empirical sidecars do not promote theorem closure; carrier mismatch diagnostics are acceptable outputs. |
| `W4` chemistry law | `L0/L1`, except known heavy photonuclear contact dependencies | Prefer direct chemistry quotient/coupling modules; avoid `AtomicPhotonuclearContactGateTheorem` unless assigned. |
| `W5` GR/QFT consumer | `L0/L1` consumer modules, `L2` for known full matter/gauge aggregates | Check `GRQFTConsumerNextObligation.agda` when the W5 next-obligation surface changes; do not run `KnownLimitsFullMatterGaugeTheorem` as an inner-loop check. |
| `W6` ITIR/PNF consumer | `L0/L1` interop and Hecke bridge modules | Check `DASHI/Interop/PNFResidualConsumerNextObligation.agda` when the W6 receipt surface changes; no live ITIR runtime validation unless explicitly assigned. |
| `W7` claim governance | docs-only or targeted proof-obligation modules | Check `ClaimGovernancePromotionObligation.agda` when governance gates change; run `TemporalSheafProofObligations.agda` only if obligation records change. |
| `W8` origin receipt | docs-only or targeted new receipt module | Check `OriginReceiptPromotionExternalObligation.agda` when the origin promotion boundary changes; do not use `Everything.agda` as routine validation for a receipt surface. |
| `W9` cancellation-pressure seam | `L0/L1` targeted delta/arithmetic modules | Check `CancellationPressureCompatibilityNextObligation.agda`, `DeltaToQuadraticBridgeTheorem.agda`, and touched arithmetic/transport modules; avoid unrelated closure aggregates. |

Board-wide smoke target:

- `DASHI/Physics/Closure/P0BlockerObligationIndex.agda` imports the current
  W1-W9 obligation/status surfaces without promoting them. Use it after
  coordination-surface edits to confirm the worker-lane index still type-checks
  before widening to lane-specific checks.

## Hygiene Script Policy

- `scripts/run_closure_hygiene.py`
- `scripts/run_closure_hygiene.sh`

These now skip learned `heavy` and `aggregator` tasks by default. Use
`--include-heavy` only for deliberate closure-certification runs with a larger
runtime budget.

## Practical Rule

Default inner loop:

1. run one or two canonical bridge modules directly
2. run `PhysicsClosureSummary.agda` if you need a broader canonical surface
3. avoid `PhysicsClosureValidationSummary.agda` unless you are explicitly doing
   a long-budget validation pass
4. treat `Everything.agda` as an occasional offline checkpoint, not a routine
   target

## Execution Stratification

Use the repo in three layers:

- `L0`: thin, interactive targets
- `L1`: bounded medium targets
- `L2`: heavy aggregate or heavy fixed-domain targets that should stay out of
  the interactive loop

Layer contract:

- `L0` / `L1` are the authoritative working surfaces for branch truth
- `L2` is the closure-certification layer
- do not mix those roles

Current policy examples:

- `L0`
  - the canonical bridge modules listed above
  - `Kernel/*.agda`
  - `Verification/*.agda`
  - `Ontology/Hecke/Layer2FiniteSearchShell.agda`
- `L1`
  - `DASHI/Physics/Closure/CanonicalStageC.agda`
  - `Ontology/Hecke/SaturatedInvariantRefinementStatus.agda`
- `L2`
  - `DASHI/Physics/Closure/PhysicsClosureValidationSummary.agda`
  - `DASHI/Everything.agda`
  - the current heavy closure recovery lane:
    `DASHI/Physics/Closure/ShiftContractObservableTransportPrimeCompatibilityProfileInstance.agda`,
    `DASHI/Physics/Closure/ShiftObservableSignaturePressureConsumer.agda`,
    `DASHI/Physics/DashiDynamicsShiftInstance.agda`,
    `DASHI/Physics/Closure/CanonicalAbstractGaugeMatterInstance.agda`,
    `DASHI/Physics/Closure/CanonicalGaugeMatterStrengtheningTheorem.agda`,
    `DASHI/Physics/Closure/KnownLimitsFullMatterGaugeTheorem.agda`,
    `DASHI/Physics/Closure/AtomicPhotonuclearContactGateTheorem.agda`,
    `DASHI/Physics/Closure/CanonicalP2KeyScheduleBridgeObstruction.agda`, and
    `DASHI/Physics/Closure/CanonicalScheduleIndependentNaturalChargeNextIngredientGap.agda`
  - the current heavy Hecke Layer 2 implementation lane:
    `Ontology/Hecke/DefectOrbitSummaryRefinement.agda`,
    `Ontology/Hecke/ForcedStableCountDecomposition.agda`,
    `Ontology/Hecke/TriadIndexedDefectOrbitSummaryRefinement.agda`,
    `Ontology/Hecke/CurrentSaturatedTriadHistogramSeparation.agda`,
    `Ontology/Hecke/CurrentSaturatedSectorHistogramComputations.agda`,
    `Ontology/Hecke/CurrentSaturatedPredictedPairComparisons.agda`,
    `Ontology/Hecke/TriadSectorCorrelationRefinement.agda`, and
    `Ontology/Hecke/Layer2FiniteSearch.agda`

Control-plane helper:

- `scripts/route_agda_by_layer.py`
- `scripts/run_agda_easy_to_hard.py`

Use it to classify one or more modules and route them as:

- interactive direct Agda runs for `L0`
- timeout-bounded Agda runs for `L1`
- queue-only or offline-certification handoff for `L2`

## Offline Closure Certification

Use exactly one aggregate target for a deliberate full closure pass:

- `DASHI/Physics/Closure/PhysicsClosureValidationSummary.agda`

Run it through:

- `scripts/run_closure_full_check.sh`

Valid outcomes are only:

1. `clean`
2. `error`
3. `too_large`

Do not interpret an `L2` timeout as a branch-classification failure.

Use `scripts/run_agda_easy_to_hard.py` when the task is not “classify this one
target” but “run the current validated easiest-to-hardest sequence”.
Its default order is:

1. `Ontology/Hecke/Layer2FiniteSearchShell.agda`
2. `Kernel/Monoid.agda`
3. `Verification/Prelude.agda`
4. `DASHI/Physics/Closure/CanonicalPrimeSelectionBridge.agda`
5. `DASHI/Physics/Closure/CanonicalPrimeInvariance.agda`
6. `DASHI/Physics/Closure/CanonicalPrimeConcentration.agda`
7. `DASHI/Physics/Closure/CanonicalPrimeSelector.agda`
8. `DASHI/Physics/Closure/CanonicalPrimeIsolation.agda`

Optional flags then extend the run with:

- bounded medium targets such as
  `Ontology/Hecke/SaturatedInvariantRefinementStatus.agda`
- Layer 2 queue generation only, not heavy theorem-lane execution
