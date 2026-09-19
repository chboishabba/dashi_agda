module DASHI.Physics.Closure.NSOpenAI2026ReleasedComparatorCanonicalShapeExact where

------------------------------------------------------------------------
-- C/D RELEASED COMPARATOR SHAPE -> DASHI CANONICAL HISTORY SHAPE
--
-- Inspected external source:
--   openai/NavierStokesAndEuler
--   NavierStokes/ComparatorTheorem.lean
--   NavierStokes/ComparatorR3Theorem.lean
--
-- Both released theorem surfaces use
--
--   u0 : Space -> Space
--   f  : Space -> Real -> Space
--   v  : Space -> Real -> Space
--   p  : Space -> Real -> Real
--
-- whereas DASHI's hardened canonical carrier uses time-first histories:
--
--   ForcingHistory  = Time -> Space -> Space
--   VelocityHistory = Time -> Space -> Space
--   PressureHistory = Time -> Space -> Real.
--
-- This owner pays that representation difference exactly by currying/argument
-- transposition.  It is deliberately scalar-backend agnostic: the still-open
-- cross-prover seam is Mathlib Real/EuclideanSpace(Fin 3) -> Bishop Real/R3,
-- not the x,t ordering.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSCanonicalEuclideanPeriodicSemanticCarriersExact as Canonical

ReleasedInitialFieldShape : Set
ReleasedInitialFieldShape = Canonical.R3Point → Canonical.R3Vector

ReleasedVectorHistoryShape : Set
ReleasedVectorHistoryShape =
  Canonical.R3Point → Canonical.Time → Canonical.R3Vector

ReleasedScalarHistoryShape : Set
ReleasedScalarHistoryShape =
  Canonical.R3Point → Canonical.Time → Canonical.BishopReal.ℝ

releasedVectorHistoryToCanonical :
  ReleasedVectorHistoryShape →
  Canonical.VelocityHistory
releasedVectorHistoryToCanonical history time point =
  history point time

canonicalVectorHistoryToReleased :
  Canonical.VelocityHistory →
  ReleasedVectorHistoryShape
canonicalVectorHistoryToReleased history point time =
  history time point

releasedPressureHistoryToCanonical :
  ReleasedScalarHistoryShape →
  Canonical.PressureHistory
releasedPressureHistoryToCanonical history time point =
  history point time

canonicalPressureHistoryToReleased :
  Canonical.PressureHistory →
  ReleasedScalarHistoryShape
canonicalPressureHistoryToReleased history point time =
  history time point

releasedForcingToCanonical :
  ReleasedVectorHistoryShape →
  Canonical.ForcingHistory
releasedForcingToCanonical history time point =
  history point time

canonicalForcingToReleased :
  Canonical.ForcingHistory →
  ReleasedVectorHistoryShape
canonicalForcingToReleased history point time =
  history time point

vectorHistoryRoundTripAt :
  (history : ReleasedVectorHistoryShape) →
  (point : Canonical.R3Point) →
  (time : Canonical.Time) →
  canonicalVectorHistoryToReleased
    (releasedVectorHistoryToCanonical history) point time
  ≡ history point time
vectorHistoryRoundTripAt history point time = refl

canonicalVectorHistoryRoundTripAt :
  (history : Canonical.VelocityHistory) →
  (time : Canonical.Time) →
  (point : Canonical.R3Point) →
  releasedVectorHistoryToCanonical
    (canonicalVectorHistoryToReleased history) time point
  ≡ history time point
canonicalVectorHistoryRoundTripAt history time point = refl

pressureHistoryRoundTripAt :
  (history : ReleasedScalarHistoryShape) →
  (point : Canonical.R3Point) →
  (time : Canonical.Time) →
  canonicalPressureHistoryToReleased
    (releasedPressureHistoryToCanonical history) point time
  ≡ history point time
pressureHistoryRoundTripAt history point time = refl

forcingHistoryRoundTripAt :
  (history : ReleasedVectorHistoryShape) →
  (point : Canonical.R3Point) →
  (time : Canonical.Time) →
  canonicalForcingToReleased
    (releasedForcingToCanonical history) point time
  ≡ history point time
forcingHistoryRoundTripAt history point time = refl

releasedComparatorSpaceTimeOrientationPaid : Bool
releasedComparatorSpaceTimeOrientationPaid = true

releasedInitialFieldShapeMatchesCanonicalAfterScalarBridge : Bool
releasedInitialFieldShapeMatchesCanonicalAfterScalarBridge = true

mathlibRealToBishopRealSameObjectClosedHere : Bool
mathlibRealToBishopRealSameObjectClosedHere = false

mathlibEuclideanSpaceToCanonicalR3ClosedHere : Bool
mathlibEuclideanSpaceToCanonicalR3ClosedHere = false

externalLeanProofImportedIntoAgda : Bool
externalLeanProofImportedIntoAgda = false

clayPromotion : Bool
clayPromotion = false

releasedComparatorSpaceTimeOrientationPaidIsTrue :
  releasedComparatorSpaceTimeOrientationPaid ≡ true
releasedComparatorSpaceTimeOrientationPaidIsTrue = refl

externalLeanProofImportedIntoAgdaIsFalse :
  externalLeanProofImportedIntoAgda ≡ false
externalLeanProofImportedIntoAgdaIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
