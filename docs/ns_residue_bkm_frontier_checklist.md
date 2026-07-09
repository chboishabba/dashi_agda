# NS Residue/BKM Frontier Checklist

Date: 2026-07-10

## Purpose

This note compresses the live NS frontier after the profile-cross / weighted
Schur route. It is keyed to the exact repo files, records, and fields that
still need mathematical inhabitants.

It is a working checklist only. It does not claim any new theorem closure.

## Current state

Structurally wired on the active chain:

- profile decomposition
- full 16-entry profile cross-product matrix
- weighted Schur product route
- `PairIncidence C/N` receipt surface

Still open on the active chain:

- actual Stage 3 pair-incidence operator witness
- `ResidueScaleCompatibility`
- residue-to-PDE shell bridge
- residence / projection / BKM analytic bridges

The active mathematical blocker is upstream of the BKM chain:

- the repo has a `PairIncidence C/N` theorem surface;
- the actual operator witness exposing the same operator used by weighted Schur
  is still fail-closed;
- `ResidueScaleCompatibility` remains downstream of that witness.

The current frontier is therefore:

1. actual Stage 3 operator witness
2. `ResidueScaleCompatibility`
3. q-gap / residue PDE bridge
4. residence / projection / BKM bridges

## Already wired

These surfaces now exist and should be treated as consumers waiting for real
analytic inhabitants, not as missing bookkeeping.

### Shell carrier semantics

File:

- `DASHI/Physics/ClaySupportingShellCarrierIdentification.agda`

Ready surfaces:

- `ShellCarrier`
- `ShellCarrierFamily`
- `NSDissipationShellBudgetInput`
- `MarkovResidenceCarrierBridge`
- `ResidueN2CarrierBridge`
- `ProjectionSummabilityCarrierBridge`

Important status:

- `danger ≤ residue` is now carrier semantics, not a separate ambient leaf.
- `dangerResidueFromCarrierSemantics` is canonical.

### BKM target wiring

File:

- `DASHI/Physics/ClaySupportingBKMClosureWiring.agda`

Ready target constructors:

- `integratedResidueN2Target`
- `residenceExclusionTarget`
- `bkmProjectionSmallnessTarget`
- `continuationFromProjectionSumWired`

Interpretation:

- the closure pipeline is present;
- the remaining work is inhabiting the PDE-facing bridges it consumes.

## Live theorem frontier

## 1. Blocker 2A: actual Stage 3 operator witness

Primary file:

- `DASHI/Physics/Closure/NSTriadKNPairIncidenceCNTheorem.agda`

The next real object is:

- `Stage3PairIncidenceOperatorWitness`

Required fields already exposed by the surface:

- `weightedSchurWitness`
- `operatorWitness`
- `sameOperatorAsWeightedSchur`

Inside the operator witness, the live mathematical leaves are:

- `absQuadraticFormDef`
- `operatorNormControlsQuadratic`

What remains false in substance:

- the current unit-shell witness is still model-only;
- the exact Stage 3 operator is not yet represented as a typed inhabitant.

Immediate deliverable:

- replace the trivial `UnitShellPairIncidenceOperatorWitnessTarget` model path
  with an actual witness for the exact weighted-Schur-controlled operator.

Exact fail-closed booleans in this file:

- `pairIncidenceOperatorWitnessClosed = false`
- `actualUnitShellPairIncidenceOperatorWitnessClosed = false`
- `actualPairIncidenceOperatorExposed = false`
- `unitShellWitnessMatchesStage3OperatorClosed = false`

## 2. Blocker 2 proper: inhabit `ResidueScaleCompatibility`

Primary file:

- `DASHI/Physics/Closure/NSTriadKNQGapTransfer.agda`

The controlling record is:

- `ResidueScaleCompatibility`

Its real mathematical content is split into two packages.

### Weak/strong scaling package

Surface:

- `WeakStrongNormScaling`

Must be inhabited by real mathematics, not placeholders:

- `operatorWeakCN`
- `weakStrongN1`
- `operatorCNToStrongErrorN2`

Interpretation:

- `|⟨L_N x , x⟩| ≤ C / N * weakNorm^2`
- `weakNorm^2 ≤ C / N * strongNorm^2`
- therefore operator error is `O(N^-2)` in the strong norm

### Base-gap minus error package

Surface:

- `BaseGapMinusErrorAbsorption`

Must be inhabited by real mathematics:

- `baseGapN2`
- `operatorErrorN2`
- `errorIdentifiedWithOperatorStrongError`
- `gapMarginPositive`
- `gapPerturbationAbsorption`

Interpretation:

- base gap lower bound
- operator error upper bound
- identification of the error term with the operator-produced strong error
- positive margin `A > B`
- absorption giving `q_gap(N) ≥ c / N^2`

Required outcome:

- construct a nontrivial `canonicalCompatibility : ResidueScaleCompatibility`
- make `compatibilityRouteClosed` true only after the real route is inhabited

## 3. q-gap to residue PDE bridge

Plan section:

- `ns_plan.txt`, Blocker 2 / section F

Repo-side consumer file:

- `DASHI/Physics/ClaySupportingShellCarrierIdentification.agda`

The key bridge to inhabit is:

- `ResidueN2CarrierBridge`

Its exact field:

- `residueN2Bound : (N : Nat) (x : ShellCarrier N) -> (N * N) * residueIntegrated x ≤ C_res * weakSq x`

Math still needed:

- identify the shell residue functional produced by the q-gap / Schur route;
- prove the shellwise `N^2` residue estimate in the carrier language.

This becomes active only after Stage 3 and `ResidueScaleCompatibility` are
real. It is the first PDE-facing theorem that actually feeds the new BKM
support chain.

## 4. Residence-time bridge

Plan section:

- `ns_plan.txt`, section G2

Repo-side consumer file:

- `DASHI/Physics/ClaySupportingShellCarrierIdentification.agda`

The bridge to inhabit is:

- `MarkovResidenceCarrierBridge`

Its exact field:

- `markov : (N : Nat) -> thresholds N * resTimes N ≤ dangerFamily c N`

Math still needed:

- define the dangerous set / threshold semantics;
- prove the Markov or Chebyshev estimate in the carrier language.

Note:

- the algebra from danger to residence exclusion is already wired;
- the missing part is the actual PDE measure estimate.

## 5. Projection smallness bridge

Plan section:

- `ns_plan.txt`, sections G1 and G2

Repo-side consumer files:

- `DASHI/Physics/ClaySupportingShellCarrierIdentification.agda`
- `DASHI/Physics/ClaySupportingBKMClosureWiring.agda`

The bridge to inhabit is:

- `ProjectionSummabilityCarrierBridge`

Its exact fields:

- `perShellN2Bound`
- `groundBound`

The remaining shellwise theorem in the wiring is:

- the argument passed to `bkmProjectionSmallnessTarget`
- type:
  `(N : Nat) (x : ShellCarrier N) -> integratedDanger x ≤ C_budget * projectionTerm x`

Math still needed:

- define the projection term as the genuine BKM-facing shell quantity;
- prove that the dangerous contribution is controlled by that projection term;
- prove the `N^2` weighted summability bound.

## 6. BKM integral bridge and continuation

Plan section:

- `ns_plan.txt`, section G3

Repo-side files:

- `DASHI/Physics/ClaySupportingBKMIntegralBridge.agda`
- `DASHI/Physics/ClaySupportingBKMContinuation.agda`
- `DASHI/Physics/ClaySupportingBKMClosureWiring.agda`

The remaining nontrivial imports to supply are:

- `BKMIntegralBridge`
- `BKMCriterionHypothesis`

Exact content:

- `BKMIntegralBridge.bridgeBound`
- `BKMCriterionHypothesis.continuationFromFiniteIntegral`

Math still needed:

- prove the shell projection sum controls the vorticity-sup integral;
- then consume the BKM criterion as the final continuation step.

## Suggested proof order

Use this order unless a new dependency forces a change:

1. `Stage3PairIncidenceOperatorWitness`
2. `ResidueScaleCompatibility`
3. `qGapControlsResidue` / `residueScaleSummability`
4. `ResidueN2CarrierBridge`
5. `MarkovResidenceCarrierBridge`
6. `ProjectionSummabilityCarrierBridge`
7. shellwise danger-to-projection bound for `bkmProjectionSmallnessTarget`
8. `BKMIntegralBridge`
9. `BKMCriterionHypothesis` consumption

Reason:

- steps 1 and 2 are the actual analytic bottleneck;
- step 3 is the first post-Blocker-2 theorem from `ns_plan.txt` section F;
- steps 4 to 9 are PDE-facing consumers of that bottleneck.

## Not the next task

Do not treat these as the live blocker for this route:

- profile cross-product bookkeeping
- another target-closed wrapper
- promotion booleans
- `clayNavierStokesPromoted`
- re-proving the already wired danger-to-residence algebra

## Cross-check against `ns_plan.txt`

The most relevant sections are:

- Blocker 2 / `ResidueScaleCompatibility`
- Schur residue scale
- BKM residence bridge

Use `ns_plan.txt` for extended mathematical prose.
Use this checklist for the exact repo work surfaces.
