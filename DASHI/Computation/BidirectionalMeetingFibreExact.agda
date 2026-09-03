module DASHI.Computation.BidirectionalMeetingFibreExact where

-- Bidirectional-search fibre: forward and reverse frontier representations may
-- vary while a consumer observes only their lower bounds and the best meeting
-- certificate.  The meeting/cut certificate is retained explicitly; it is not
-- erased by quotienting the two frontier tails.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

record BidirectionalFineState : Set where
  constructor bidirectionalFineState
  field
    forwardLowerBound reverseLowerBound : Nat
    bestMeetingCost : Nat
    forwardTailCode reverseTailCode : Bool

open BidirectionalFineState public

record BidirectionalObservation : Set where
  constructor bidirectionalObservation
  field
    observedForwardLowerBound : Nat
    observedReverseLowerBound : Nat
    observedBestMeetingCost : Nat

observeBidirectional : BidirectionalFineState → BidirectionalObservation
observeBidirectional s =
  bidirectionalObservation
    (forwardLowerBound s)
    (reverseLowerBound s)
    (bestMeetingCost s)

data FrontierTailSwap : Set where
  identityFrontierTail
  swapForwardTail
  swapReverseTail
  swapBothTails : FrontierTailSwap

flip : Bool → Bool
flip false = true
flip true = false

actFrontierTail : FrontierTailSwap → BidirectionalFineState → BidirectionalFineState
actFrontierTail identityFrontierTail s = s
actFrontierTail swapForwardTail (bidirectionalFineState f r m ft rt) =
  bidirectionalFineState f r m (flip ft) rt
actFrontierTail swapReverseTail (bidirectionalFineState f r m ft rt) =
  bidirectionalFineState f r m ft (flip rt)
actFrontierTail swapBothTails (bidirectionalFineState f r m ft rt) =
  bidirectionalFineState f r m (flip ft) (flip rt)

frontierTailActionPreservesObservation :
  (g : FrontierTailSwap) (s : BidirectionalFineState) →
  observeBidirectional (actFrontierTail g s) ≡ observeBidirectional s
frontierTailActionPreservesObservation identityFrontierTail s = refl
frontierTailActionPreservesObservation swapForwardTail (bidirectionalFineState f r m ft rt) = refl
frontierTailActionPreservesObservation swapReverseTail (bidirectionalFineState f r m ft rt) = refl
frontierTailActionPreservesObservation swapBothTails (bidirectionalFineState f r m ft rt) = refl

record BidirectionalFibreBoundary : Set where
  constructor bidirectionalFibreBoundary
  field
    twoFrontierTailOrdersMayBeResidual : Bool
    twoFrontierTailOrdersMayBeResidualIsTrue :
      twoFrontierTailOrdersMayBeResidual ≡ true
    meetingCertificateMayBeDiscarded : Bool
    meetingCertificateMayBeDiscardedIsFalse :
      meetingCertificateMayBeDiscarded ≡ false
    oneSidedCorrectnessAutomaticallyGivesBidirectionalStoppingRule : Bool
    oneSidedCorrectnessAutomaticallyGivesBidirectionalStoppingRuleIsFalse :
      oneSidedCorrectnessAutomaticallyGivesBidirectionalStoppingRule ≡ false

canonicalBidirectionalFibreBoundary : BidirectionalFibreBoundary
canonicalBidirectionalFibreBoundary =
  bidirectionalFibreBoundary true refl false refl false refl
