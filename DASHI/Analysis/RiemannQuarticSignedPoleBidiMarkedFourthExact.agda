module DASHI.Analysis.RiemannQuarticSignedPoleBidiMarkedFourthExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- RH BIDI MARKED FOURTH-ANGULAR OWNER
--
-- Lean companion:
--
--   Synthesis/
--   RiemannProjectiveQuarticFourWindowSignedPoleBidiMarkedFourth.lean
--
-- This owner records the first genuinely useful bridge between the live
-- fourth-angular RH obstruction and Montgomery-type marked pair machinery.
--
-- Backward / Clay-facing side:
--
--   A4_local
--     =
--   sum_local m_sigma Re(a_sigma + i delta_sigma)^4
--     - local smooth-mu vertical fourth moment.
--
-- The zero part splits exactly into a centred vertical fourth moment plus
-- the horizontal correction
--
--   sum m delta^4 - integral delta^4 mu
--     + sum m a^2(a^2 - 6 delta^2).
--
-- Forward / pair-difference side:
--
-- Let the target zero have horizontal displacement A and let its horizontal
-- functional-equation reflection have displacement -A.  For
--
--   P2(x,d) = Re(x+i d)^2,
--   P4(x,d) = Re(x+i d)^4,
--
-- Lean proves the pointwise identity
--
--   P4(a,d)
--     =
--   1/2 * [ P4(a-A,d) + P4(a+A,d) ]
--     - 3*A^2 * [ P2(a-A,d) + P2(a+A,d) ]
--     + 5*A^4.
--
-- Hence the local target-centred fourth angular statistic is reconstructed
-- from only the 0th, 2nd and 4th EVEN marked pair-difference moments around
-- the target and its horizontal reflection.  Odd derivatives/moments are
-- not required.
--
-- This is the current bidi intersection:
--
--   desired target-centred cos(4 theta) statistic
--       <-> even marked pair moments of orders 0,2,4.
--
-- What remains new mathematics is a one-centre LOCALIZED marked
-- pair-correlation / explicit-formula estimate strong enough to control those
-- moments with the required sign and to couple them to the exact far source.
------------------------------------------------------------------------

data BidiMarkedFourthCoordinate : Set where
  centredLocalFourthAngularDefinition : BidiMarkedFourthCoordinate
  verticalPlusHorizontalCentredSplit : BidiMarkedFourthCoordinate
  targetReflectionPointwiseFourthReconstruction :
    BidiMarkedFourthCoordinate
  evenZeroTwoFourMarkedMomentsSuffice :
    BidiMarkedFourthCoordinate

  localizedOneCentreMarkedPairProducer :
    BidiMarkedFourthCoordinate
  markedPairPrimeSideSignOrBound :
    BidiMarkedFourthCoordinate
  centredFourthAngularBias :
    BidiMarkedFourthCoordinate
  fourthAngularFarCouplingPaysG3 :
    BidiMarkedFourthCoordinate

data BidiMarkedFourthStatus : Set where
  theoremOwned : BidiMarkedFourthStatus
  openAnalyticObstruction : BidiMarkedFourthStatus

bidiMarkedFourthStatus :
  BidiMarkedFourthCoordinate -> BidiMarkedFourthStatus
bidiMarkedFourthStatus centredLocalFourthAngularDefinition = theoremOwned
bidiMarkedFourthStatus verticalPlusHorizontalCentredSplit = theoremOwned
bidiMarkedFourthStatus targetReflectionPointwiseFourthReconstruction =
  theoremOwned
bidiMarkedFourthStatus evenZeroTwoFourMarkedMomentsSuffice = theoremOwned

bidiMarkedFourthStatus localizedOneCentreMarkedPairProducer =
  openAnalyticObstruction
bidiMarkedFourthStatus markedPairPrimeSideSignOrBound =
  openAnalyticObstruction
bidiMarkedFourthStatus centredFourthAngularBias =
  openAnalyticObstruction
bidiMarkedFourthStatus fourthAngularFarCouplingPaysG3 =
  openAnalyticObstruction

record BidiMarkedFourthBoundary : Set where
  constructor bidi-marked-fourth-boundary
  field
    centredLocalFourthAngularDefinitionPaid : Bool
    verticalPlusHorizontalCentredSplitPaid : Bool
    targetReflectionPointwiseFourthReconstructionPaid : Bool
    evenZeroTwoFourMarkedMomentsSufficePaid : Bool

    localizedOneCentreMarkedPairProducerPaid : Bool
    markedPairPrimeSideSignOrBoundPaid : Bool
    centredFourthAngularBiasPaid : Bool
    fourthAngularFarCouplingPaysG3Paid : Bool

    centredLocalFourthAngularDefinitionPaidIsTrue :
      centredLocalFourthAngularDefinitionPaid ≡ true
    verticalPlusHorizontalCentredSplitPaidIsTrue :
      verticalPlusHorizontalCentredSplitPaid ≡ true
    targetReflectionPointwiseFourthReconstructionPaidIsTrue :
      targetReflectionPointwiseFourthReconstructionPaid ≡ true
    evenZeroTwoFourMarkedMomentsSufficePaidIsTrue :
      evenZeroTwoFourMarkedMomentsSufficePaid ≡ true

    localizedOneCentreMarkedPairProducerPaidIsFalse :
      localizedOneCentreMarkedPairProducerPaid ≡ false
    markedPairPrimeSideSignOrBoundPaidIsFalse :
      markedPairPrimeSideSignOrBoundPaid ≡ false
    centredFourthAngularBiasPaidIsFalse :
      centredFourthAngularBiasPaid ≡ false
    fourthAngularFarCouplingPaysG3PaidIsFalse :
      fourthAngularFarCouplingPaysG3Paid ≡ false

    interpretation : String
    nextResearchCut : String

canonicalBidiMarkedFourthBoundary :
  BidiMarkedFourthBoundary
canonicalBidiMarkedFourthBoundary =
  bidi-marked-fourth-boundary
    true true true true
    false false false false
    refl refl refl refl
    refl refl refl refl
    "The live RH obstruction is now expressed both backward from G3 as a smooth-mu-centred fourth angular statistic and forward toward Montgomery machinery as even target/reflection marked pair moments.  The exact algebraic bridge needs only orders 0, 2 and 4: P4(a,d)=1/2(P4(a-A,d)+P4(a+A,d))-3*A^2(P2(a-A,d)+P2(a+A,d))+5*A^4.  This removes the apparent need for odd marked derivatives and identifies a concrete same-object interface for a localized pair-correlation theorem."
    "Do not add more compensation bookkeeping.  The next Clay-relevant mathematics is a target-centred localized marked pair producer, together with a prime-side estimate strong enough to control its even 2nd/4th moments uniformly around an arbitrary hypothetical off-line zero.  Preserve FarExact with sign.  If this marked local theorem cannot be obtained, redesign the witness rather than adding representation layers."

targetReflectionBidiBridgeIsPaid :
  bidiMarkedFourthStatus targetReflectionPointwiseFourthReconstruction
    ≡ theoremOwned
targetReflectionBidiBridgeIsPaid = refl

evenMarkedMomentsAreTheInterface :
  bidiMarkedFourthStatus evenZeroTwoFourMarkedMomentsSuffice
    ≡ theoremOwned
evenMarkedMomentsAreTheInterface = refl

localizedMarkedPairProducerRemainsOpen :
  bidiMarkedFourthStatus localizedOneCentreMarkedPairProducer
    ≡ openAnalyticObstruction
localizedMarkedPairProducerRemainsOpen = refl
