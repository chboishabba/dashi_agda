module DASHI.Physics.Closure.UnificationCrossTermToModuloNullConsumerCompositeLightweightBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.UnificationCrossTermChildCompositeLightweightBoundary
  as Child
import DASHI.Physics.Closure.UnificationNullTransportModuloNullConsumerLightweightBoundary
  as Consumer
import DASHI.Physics.Closure.UnificationModuloNullLinearityFromCrossTermNullityBoundary
  as ModuloNull

record UnificationCrossTermToModuloNullConsumerCompositeLightweightBoundary : Set where
  field
    childComposite :
      Child.UnificationCrossTermChildCompositeLightweightBoundary
    childCompositeIsCanonical :
      childComposite ≡ Child.canonicalUnificationCrossTermChildCompositeLightweightBoundary
    consumerBoundary :
      Consumer.UnificationNullTransportModuloNullConsumerLightweightBoundary
    consumerBoundaryIsCanonical :
      consumerBoundary
        ≡ Consumer.canonicalUnificationNullTransportModuloNullConsumerLightweightBoundary
    moduloNullRouteReferenceRecorded :
      Bool
    moduloNullRouteReferenceRecordedIsTrue :
      moduloNullRouteReferenceRecorded ≡ true
    childStillFalse :
      Child.UnificationCrossTermChildCompositeLightweightBoundary.crossTermStillFalse
        Child.canonicalUnificationCrossTermChildCompositeLightweightBoundary ≡ refl
    consumerStillFalse :
      Consumer.NullTransportModuloNullConsumerProvedLightweight ≡ false
    terminalStillFalse :
      ModuloNull.terminalUnificationPromoted
        ModuloNull.canonicalUnificationModuloNullLinearityFromCrossTermNullityBoundary ≡ false

canonicalUnificationCrossTermToModuloNullConsumerCompositeLightweightBoundary :
  UnificationCrossTermToModuloNullConsumerCompositeLightweightBoundary
canonicalUnificationCrossTermToModuloNullConsumerCompositeLightweightBoundary =
  record
    { childComposite =
        Child.canonicalUnificationCrossTermChildCompositeLightweightBoundary
    ; childCompositeIsCanonical = refl
    ; consumerBoundary =
        Consumer.canonicalUnificationNullTransportModuloNullConsumerLightweightBoundary
    ; consumerBoundaryIsCanonical = refl
    ; moduloNullRouteReferenceRecorded = true
    ; moduloNullRouteReferenceRecordedIsTrue = refl
    ; childStillFalse = refl
    ; consumerStillFalse = refl
    ; terminalStillFalse = refl
    }
