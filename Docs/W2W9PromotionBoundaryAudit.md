# W2/W9 Promotion Boundary Audit

Date: 2026-05-12

Scope: bounded documentation audit of the current local W2 and W9 promotion
boundaries. This document records blockers only. It does not construct a token,
close a promotion lane, fabricate a kill receipt, or reinterpret an accepted
retarget consumer as a W9 kill receipt.

## Files Found

- `DASHI/Physics/Closure/NaturalP2ConvergencePromotionObligation.agda`
- `DASHI/Physics/Closure/W2PromotionAuthorityReceipt.agda`
- `DASHI/Physics/Closure/W9PairTransportBridgeObstruction.agda`
- `DASHI/Physics/Closure/CancellationPressureCompatibilityNextObligation.agda`
- `DASHI/Physics/Closure/W9WeightedSupportRetargetConsumerReceipt.agda`

## W2 Boundary

Current blocker: `NaturalP2ConvergencePromotionAuthorityToken` is still
constructorless. The local positive arithmetic support is not enough to issue
`NaturalP2ConvergencePromotionReceipt`.

Evidence:

- `NaturalP2ConvergencePromotionObligation.agda:28` declares
  `data NaturalP2ConvergencePromotionAuthorityToken : Set where` with no
  constructors.
- `NaturalP2ConvergencePromotionObligation.agda:83-101` requires a
  `promotionAuthority : NaturalP2ConvergencePromotionAuthorityToken` inside
  `NaturalP2ConvergencePromotionReceipt`.
- `NaturalP2ConvergencePromotionObligation.agda:103-111` proves
  `naturalP2ConvergencePromotionAuthorityUnavailable` and eliminates any
  `NaturalP2ConvergencePromotionReceipt` through that authority field.
- `W2PromotionAuthorityReceipt.agda:48-79` records
  `canonicalW2PromotionAuthorityAuditDiagnostic`; its remaining fields include
  `missingPromotionAuthorityToken`, natural P2 bridge packaging, carrier
  transport law, and carrier-general realization-uniform convergence-rate
  receipt.

Exact current status: W2 remains non-promoted. The landed
`naturalP2NormalizeAddSumInvariant` and local uniform-rate support are positive
ingredients, but the authority token gap is the promotion boundary.

## W9 Boundary

Current blocker: the pair route is obstructed, the weighted replacement route
is obstructed, and the retarget receipt is accepted-only. The retarget status is
not a `W9KillReceipt`.

Evidence:

- `CancellationPressureCompatibilityNextObligation.agda:37-60` defines the
  existing route as `ExistingCancellationPressureCompatibilityObligation`,
  requiring the pointwise `pressureWitness` consumed by
  `DQ.canonicalCancellationPressureCompatibility`.
- `CancellationPressureCompatibilityNextObligation.agda:110-116` identifies
  the weighted replacement seam:
  `cancellationPressureIdentifiesWeightedQuadraticEnergy`.
- `CancellationPressureCompatibilityNextObligation.agda:246-295` records the
  canonical-15 pair-route mismatch at `(one , three)` and
  `canonical15ExistingPressureWitnessObstruction`.
- `CancellationPressureCompatibilityNextObligation.agda:316-345` records
  route-class exhaustion with existing route counterexample `(one , three)` and
  weighted route counterexample `(one , one)`.
- `CancellationPressureCompatibilityNextObligation.agda:410-423` records
  `canonicalPairPressureRetargetReceipt` with
  `selectedNextRoute = supplyPressureCompatibleTargetWithQcoreBoundary` and
  `nonPromotionBoundary = retargetMustNotClaimCanonicalQcore`.
- `W9WeightedSupportRetargetConsumerReceipt.agda:65-67` defines the only local
  retarget scope constructor as `retargetConsumerAcceptedOnly`.
- `W9WeightedSupportRetargetConsumerReceipt.agda:104-127` inhabits
  `canonicalWeightedSupportRetargetConsumerReceipt` but explicitly lists that
  no dim-15 pressure witness, no `CancellationPressureCompatibility`, and no W9
  kill receipt are constructed.
- `W9PairTransportBridgeObstruction.agda:39-47` includes the status
  `retargetAcceptedOnlyNoW9KillReceipt`.
- `W9PairTransportBridgeObstruction.agda:111-152` records the current
  obstruction: `Kill.w9KillCondition` is still blocked, both accepted routes
  are rejected by local counterexamples, the retarget consumer scope is
  accepted-only, and no `W9KillReceipt` is constructed.

Exact current status: W9 remains blocked. The first missing bridge is from the
available weighted-support/retarget consumer surface into an accepted W9 kill
route, either by inhabiting the existing pair pressure witness, supplying the
weighted cancellation-to-quadratic identification, or adding an explicitly
accepted kill route for the retarget-only receipt. This audit does not attempt
any of those.

## Targeted Validation

Commands run from `/home/c/Documents/code/dashi_agda`:

```sh
agda -i . -l standard-library DASHI/Physics/Closure/W2PromotionAuthorityReceipt.agda
agda -i . -l standard-library DASHI/Physics/Closure/W9PairTransportBridgeObstruction.agda
```

Both targeted commands exited with status 0 and produced no diagnostic output.

Useful follow-up validation commands for this boundary, if the audited surfaces
change:

```sh
agda -i . -l standard-library DASHI/Physics/Closure/NaturalP2ConvergencePromotionObligation.agda
agda -i . -l standard-library DASHI/Physics/Closure/CancellationPressureCompatibilityNextObligation.agda
agda -i . -l standard-library DASHI/Physics/Closure/W9WeightedSupportRetargetConsumerReceipt.agda
```
