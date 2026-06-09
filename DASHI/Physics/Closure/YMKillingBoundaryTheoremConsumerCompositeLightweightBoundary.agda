module DASHI.Physics.Closure.YMKillingBoundaryTheoremConsumerCompositeLightweightBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.YMKillingBoundaryChildProofCompositeLightweightBoundary
  as Child
import DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessTheoremBoundary
  as Theorem
import DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessTheoremLadderBoundary
  as Ladder

record YMKillingBoundaryTheoremConsumerCompositeLightweightBoundary : Set where
  field
    childComposite :
      Child.YMKillingBoundaryChildProofCompositeLightweightBoundary
    childCompositeIsCanonical :
      childComposite ≡ Child.canonicalYMKillingBoundaryChildProofCompositeLightweightBoundary
    theoremBoundary :
      Theorem.YMKillingBoundarySelfAdjointnessTheoremBoundary
    theoremBoundaryIsCanonical :
      theoremBoundary ≡ Theorem.canonicalYMKillingBoundarySelfAdjointnessTheoremBoundary
    theoremLadder :
      Ladder.YMKillingBoundarySelfAdjointnessTheoremLadderBoundary
    theoremLadderIsCanonical :
      theoremLadder ≡ Ladder.canonicalYMKillingBoundarySelfAdjointnessTheoremLadderBoundary
    consumerCompositeRecorded :
      Bool
    consumerCompositeRecordedIsTrue :
      consumerCompositeRecorded ≡ true
    theoremStillFalse :
      Theorem.YMKillingBoundarySelfAdjointnessTheoremProved ≡ false
    ladderStillFalse :
      Ladder.YMTheoremLadderPromoted ≡ false
    ymClayStillFalse :
      Theorem.YMClayPromotedFromYM1 ≡ false

canonicalYMKillingBoundaryTheoremConsumerCompositeLightweightBoundary :
  YMKillingBoundaryTheoremConsumerCompositeLightweightBoundary
canonicalYMKillingBoundaryTheoremConsumerCompositeLightweightBoundary =
  record
    { childComposite =
        Child.canonicalYMKillingBoundaryChildProofCompositeLightweightBoundary
    ; childCompositeIsCanonical = refl
    ; theoremBoundary =
        Theorem.canonicalYMKillingBoundarySelfAdjointnessTheoremBoundary
    ; theoremBoundaryIsCanonical = refl
    ; theoremLadder =
        Ladder.canonicalYMKillingBoundarySelfAdjointnessTheoremLadderBoundary
    ; theoremLadderIsCanonical = refl
    ; consumerCompositeRecorded = true
    ; consumerCompositeRecordedIsTrue = refl
    ; theoremStillFalse = refl
    ; ladderStillFalse = refl
    ; ymClayStillFalse = refl
    }

