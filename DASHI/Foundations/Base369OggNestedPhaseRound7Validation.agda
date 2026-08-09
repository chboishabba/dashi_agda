module DASHI.Foundations.Base369OggNestedPhaseRound7Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)

open import Base369 using
  ( non-0
  ; non-1
  ; non-8
  )

open import DASHI.Foundations.SSPTritCarrier using
  ( SSPTrit
  ; sspNegOne
  ; sspZero
  ; sspPosOne
  )

import DASHI.Foundations.Base369NonaryTritSquareExact as Square
import DASHI.Foundations.Base369CompletedRelationalDigitExact as Completed
import DASHI.Foundations.Base369FiveModePhaseQuotientExact as Five
import DASHI.Foundations.Base369RelationalSymmetryRealisationExact as Realisation
import DASHI.Foundations.Base369PhaseCompletionAndNestedEvaluationExact as Phase
import DASHI.Moonshine.MonsterOggNonarySSPTritBridgeExact as Bridge
import DASHI.Moonshine.Monster3BBalancedRegularFibreExact as Fibre
import DASHI.Moonshine.MonsterOggPrimaryDepthAndNestedEigenCarrierExact as Nested
import DASHI.Moonshine.MonsterFivePrimaryRelationalModelBoundaryExact as FiveBoundary
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

nonarySquareRoundTripAtEight :
  Square.tritSquareToNonaryDigit
    (Square.nonaryDigitToTritSquare non-8)
  ≡ non-8
nonarySquareRoundTripAtEight = refl

lowTritOneIsPositive :
  Square.nonaryDigitToLowTrit non-1 ≡ sspPosOne
lowTritOneIsPositive = refl

lowTritEightIsNegative :
  Square.nonaryDigitToLowTrit non-8 ≡ sspNegOne
lowTritEightIsNegative = refl

complementReversesOneToEight :
  Square.nonaryDigitToLowTrit
    (Square.complementNonaryDigit non-1)
  ≡ Square.negateSSPTrit (Square.nonaryDigitToLowTrit non-1)
complementReversesOneToEight = refl

emptyZeroAndCompletedNineShareAddress :
  Completed.address (Completed.digit Completed.emptyZeroDigit)
  ≡ Completed.address (Completed.digit Completed.completedNineDigit)
emptyZeroAndCompletedNineShareAddress = refl

completedNineHasDistinctCompletionCoordinate :
  Completed.completion Completed.completedNineDigit
  ≡ Completed.instantiated
completedNineHasDistinctCompletionCoordinate = refl

fiveModesTwoPhasesPointedRoundTrip :
  Five.orientedModeToPointedNonary
    (Five.pointedNonaryToOrientedMode Five.completionJ)
  ≡ Five.completionJ
fiveModesTwoPhasesPointedRoundTrip = refl

identityModeOrientationsQuotientTogether :
  Five.quotientOrientedMode
    (Five.orientedMode Five.A1 Five.negativeOrientation)
  ≡ Five.quotientOrientedMode
      (Five.orientedMode Five.A1 Five.positiveOrientation)
identityModeOrientationsQuotientTogether = refl

threeIsNeutralInOggTritBridge :
  Bridge.oggPrimeResidueTrit Lane.p3 ≡ sspZero
threeIsNeutralInOggTritBridge = refl

monsterFivePrimaryDepthIsNine :
  Nested.monsterPrimaryDepth Lane.p5 ≡ 9
monsterFivePrimaryDepthIsNine = refl

monsterSeventyOneIsShallowWide :
  Nested.monsterPrimaryDepth Lane.p71 ≡ 1
monsterSeventyOneIsShallowWide = refl

fiveHasTwoInversePhasePairs :
  Nested.phasePairCount Nested.odd5 ≡ 2
fiveHasTwoInversePhasePairs = refl

monster3BFineMultiplicityIs65610 :
  Fibre.monster3BRegularMultiplicity ≡ 65610
monster3BFineMultiplicityIs65610 =
  Fibre.monster3BRegularMultiplicityIs65610

monster3BIdentitySeesFullCarrier :
  Fibre.identityEvaluation Fibre.monster3BResidualRegularCarrier
  ≡ 196883
monster3BIdentitySeesFullCarrier =
  Fibre.monster3BIdentityEvaluationIs196883

monster3BNontrivialPhaseSeesResidual :
  Fibre.nontrivialPhaseEvaluation Fibre.monster3BResidualRegularCarrier
  ≡ 53
monster3BNontrivialPhaseSeesResidual =
  Fibre.monster3BNontrivialEvaluationIs53

nonaryRealisationUsesPolarityReversal :
  Realisation.observeTrit Realisation.nonaryComplementRealisation
    (Realisation.reverse Realisation.nonaryComplementRealisation non-1)
  ≡ Square.negateSSPTrit
      (Realisation.observeTrit Realisation.nonaryComplementRealisation non-1)
nonaryRealisationUsesPolarityReversal = refl

sampleBalancedPhaseFibre : Phase.BalancedPhaseFibre SSPTrit
sampleBalancedPhaseFibre =
  Phase.balancedPhaseFibre sspNegOne sspZero sspPosOne

sampleInstantiatedPhaseCompletion : Phase.PhaseCompletion SSPTrit SSPTrit
sampleInstantiatedPhaseCompletion =
  Phase.instantiatedPhaseCompletion sampleBalancedPhaseFibre sspZero

phasePromotionRetainsFineFibre :
  Phase.retainedFineFibre
    (Phase.promoteCompletedBlock zero sampleInstantiatedPhaseCompletion)
  ≡ Phase.fineFibre sampleInstantiatedPhaseCompletion
phasePromotionRetainsFineFibre = refl

fiveLocalActualCarrierRemainsOpen :
  FiveBoundary.actualFiveLocalCarrierIdentified
    FiveBoundary.canonicalMonsterFivePrimaryPromotionBoundary
  ≡ false
fiveLocalActualCarrierRemainsOpen = refl

fiveLocalNineChannelObserverRemainsOpen :
  FiveBoundary.actualNineChannelObserverConstructed
    FiveBoundary.canonicalMonsterFivePrimaryPromotionBoundary
  ≡ false
fiveLocalNineChannelObserverRemainsOpen = refl
