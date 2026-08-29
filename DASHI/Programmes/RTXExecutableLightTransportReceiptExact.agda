module DASHI.Programmes.RTXExecutableLightTransportReceiptExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Executable receipt for dashiRTX.
--
-- The satellite already separates pixel reference rendering, quadtree
-- approximation, held-out validation MAE/MDL, leaf count and runtime.  The
-- theorem-facing bridge therefore preserves the declared observation while
-- keeping approximation quality, compression and performance distinct.
------------------------------------------------------------------------

record RTXLightTransportRunReceipt : Set₁ where
  constructor rtx-light-transport-run-receipt
  field
    Scene Observation Approximation Criterion : Set

    referenceObservation : Scene → Observation
    approximateObservation : Scene → Approximation
    decodeApproximation : Approximation → Observation

    HeldOutScene : Scene → Set
    close : Observation → Observation → Criterion → Set
    criterion : Criterion

    heldOutApproximationReceipt :
      (scene : Scene) → HeldOutScene scene →
      close
        (decodeApproximation (approximateObservation scene))
        (referenceObservation scene)
        criterion

    criterionDeclaredBeforeHeldOutEvaluation : Set

open RTXLightTransportRunReceipt public

record RTXExecutableBoundary : Set where
  constructor rtx-executable-boundary
  field
    lowerValidationMAEIsPhysicalTruth : Bool
    lowerValidationMAEIsPhysicalTruthIsFalse :
      lowerValidationMAEIsPhysicalTruth ≡ false

    fewerQuadtreeLeavesIsObservationPreservation : Bool
    fewerQuadtreeLeavesIsObservationPreservationIsFalse :
      fewerQuadtreeLeavesIsObservationPreservation ≡ false

    fasterRenderIsSemanticEquivalence : Bool
    fasterRenderIsSemanticEquivalenceIsFalse :
      fasterRenderIsSemanticEquivalence ≡ false

    heldOutObservationReceiptCanSupportApproximationClaim : Bool
    heldOutObservationReceiptCanSupportApproximationClaimIsTrue :
      heldOutObservationReceiptCanSupportApproximationClaim ≡ true

canonicalRTXExecutableBoundary : RTXExecutableBoundary
canonicalRTXExecutableBoundary =
  rtx-executable-boundary
    false refl
    false refl
    false refl
    true refl
