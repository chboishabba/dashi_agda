module DASHI.Physics.Closure.UnificationCrossTermChildCompositeLightweightBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.UnificationCrossTermNullityLightweightBoundary
  as CrossTerm
import DASHI.Physics.Closure.UnificationNullClassStabilityLightweightBoundary
  as Stability

record UnificationCrossTermChildCompositeLightweightBoundary : Set where
  field
    crossTermBoundary :
      CrossTerm.UnificationCrossTermNullityLightweightBoundary
    crossTermBoundaryIsCanonical :
      crossTermBoundary ≡ CrossTerm.canonicalUnificationCrossTermNullityLightweightBoundary
    nullClassStabilityBoundary :
      Stability.UnificationNullClassStabilityLightweightBoundary
    nullClassStabilityBoundaryIsCanonical :
      nullClassStabilityBoundary
        ≡ Stability.canonicalUnificationNullClassStabilityLightweightBoundary
    childCompositeRecorded :
      Bool
    childCompositeRecordedIsTrue :
      childCompositeRecorded ≡ true
    crossTermStillFalse :
      CrossTerm.UnificationCrossTermNullityTheoremProvedLightweight ≡ false
    nullClassStillFalse :
      Stability.NullClassStabilityTheoremProvedLightweight ≡ false

canonicalUnificationCrossTermChildCompositeLightweightBoundary :
  UnificationCrossTermChildCompositeLightweightBoundary
canonicalUnificationCrossTermChildCompositeLightweightBoundary =
  record
    { crossTermBoundary =
        CrossTerm.canonicalUnificationCrossTermNullityLightweightBoundary
    ; crossTermBoundaryIsCanonical = refl
    ; nullClassStabilityBoundary =
        Stability.canonicalUnificationNullClassStabilityLightweightBoundary
    ; nullClassStabilityBoundaryIsCanonical = refl
    ; childCompositeRecorded = true
    ; childCompositeRecordedIsTrue = refl
    ; crossTermStillFalse = refl
    ; nullClassStillFalse = refl
    }

