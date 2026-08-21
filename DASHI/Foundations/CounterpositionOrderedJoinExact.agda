module DASHI.Foundations.CounterpositionOrderedJoinExact where

open import DASHI.Core.Prelude
open import DASHI.Core.ListExact public

import DASHI.Foundations.BalancedTernaryAmplitudeClosureExact as Amp
import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT
import DASHI.Foundations.StageSymmetryCarrierTowerExact as Sym

------------------------------------------------------------------------
-- Binary opposition is the zero-free subcarrier of balanced ternary.
------------------------------------------------------------------------

embedBinaryOrientation : Sym.C2 → BT.BalancedDigit
embedBinaryOrientation Sym.direct = BT.pos
embedBinaryOrientation Sym.inverse = BT.neg

binaryEmbeddingInjective :
  {left right : Sym.C2} →
  embedBinaryOrientation left ≡ embedBinaryOrientation right →
  left ≡ right
binaryEmbeddingInjective {Sym.direct} {Sym.direct} refl = refl
binaryEmbeddingInjective {Sym.direct} {Sym.inverse} ()
binaryEmbeddingInjective {Sym.inverse} {Sym.direct} ()
binaryEmbeddingInjective {Sym.inverse} {Sym.inverse} refl = refl

binaryEmbeddingNeverNeutral :
  (orientation : Sym.C2) →
  embedBinaryOrientation orientation ≡ BT.zeroDigit → ⊥
binaryEmbeddingNeverNeutral Sym.direct ()
binaryEmbeddingNeverNeutral Sym.inverse ()

data CounterContext : Set where
  invertAll rejectFirst rejectSecond rejectThird reindexFirstSecond :
    CounterContext

counterUnder : CounterContext → BT.TriadPattern → BT.TriadPattern
counterUnder invertAll triadPattern = BT.strictInverse triadPattern
counterUnder rejectFirst triadPattern =
  BT.triad
    (BT.invertDigit (BT.first triadPattern))
    (BT.second triadPattern)
    (BT.third triadPattern)
counterUnder rejectSecond triadPattern =
  BT.triad
    (BT.first triadPattern)
    (BT.invertDigit (BT.second triadPattern))
    (BT.third triadPattern)
counterUnder rejectThird triadPattern =
  BT.triad
    (BT.first triadPattern)
    (BT.second triadPattern)
    (BT.invertDigit (BT.third triadPattern))
counterUnder reindexFirstSecond triadPattern =
  BT.triad
    (BT.second triadPattern)
    (BT.first triadPattern)
    (BT.third triadPattern)

rejectThirdAllPositiveIsPartialCounterposition :
  counterUnder rejectThird BT.allPositive
  ≡ BT.thirdCoordinateCounterposition
rejectThirdAllPositiveIsPartialCounterposition = refl

partialCounterpositionIsNotFullInverse :
  counterUnder rejectThird BT.allPositive
  ≡ counterUnder invertAll BT.allPositive
  → ⊥
partialCounterpositionIsNotFullInverse ()

------------------------------------------------------------------------
-- The older counterposition result is the foundation: contextual opposition
-- need not be full inversion.  The following is only the narrower corollary
-- needed by later `!!x` notation discussions: strict inversion is involutive,
-- while the same contextual counterposition need not return the input.
------------------------------------------------------------------------

invertDigitInvolutive :
  (digit : BT.BalancedDigit) →
  BT.invertDigit (BT.invertDigit digit) ≡ digit
invertDigitInvolutive BT.neg = refl
invertDigitInvolutive BT.zeroDigit = refl
invertDigitInvolutive BT.pos = refl

strictInverseInvolutive :
  (pat : BT.TriadPattern) →
  BT.strictInverse (BT.strictInverse pat) ≡ pat
strictInverseInvolutive (BT.triad first second third)
  rewrite invertDigitInvolutive first
        | invertDigitInvolutive second
        | invertDigitInvolutive third = refl

partialCounterpositionIsNotDoubleInverse :
  counterUnder rejectThird BT.allPositive
  ≡ BT.strictInverse (BT.strictInverse BT.allPositive)
  → ⊥
partialCounterpositionIsNotDoubleInverse ()

record CounterpositionThreeWaySeparation : Set where
  constructor counterpositionThreeWaySeparation
  field
    input : BT.TriadPattern
    contextual : BT.TriadPattern
    fullInverse : BT.TriadPattern
    doubleInverse : BT.TriadPattern
    contextualExact : counterUnder rejectThird input ≡ contextual
    fullInverseExact : counterUnder invertAll input ≡ fullInverse
    doubleInverseExact : BT.strictInverse (BT.strictInverse input) ≡ doubleInverse
    contextualNotFullInverse : contextual ≡ fullInverse → ⊥
    contextualNotDoubleInverse : contextual ≡ doubleInverse → ⊥

canonicalCounterpositionThreeWaySeparation : CounterpositionThreeWaySeparation
canonicalCounterpositionThreeWaySeparation =
  counterpositionThreeWaySeparation
    BT.allPositive
    BT.thirdCoordinateCounterposition
    BT.allNegative
    BT.allPositive
    refl refl
    (strictInverseInvolutive BT.allPositive)
    (λ ())
    (λ ())

record OrderedTriadJoin : Set where
  constructor orderedTriadJoin
  field
    lower upper : BT.TriadPattern
    joinedAmplitude : Amp.JoinedAmplitude13
    joinedAmplitudeExact :
      Amp.joinAmplitude lower upper ≡ joinedAmplitude

open OrderedTriadJoin public

stageFiveLowerThenUpper : OrderedTriadJoin
stageFiveLowerThenUpper =
  orderedTriadJoin
    BT.allPositive BT.twoPositiveOneOpen Amp.joinedPos5 refl

stageFiveUpperThenLower : OrderedTriadJoin
stageFiveUpperThenLower =
  orderedTriadJoin
    BT.twoPositiveOneOpen BT.allPositive Amp.joinedPos5 refl

orderedStageFiveJoinsShareAmplitude :
  joinedAmplitude stageFiveLowerThenUpper
  ≡ joinedAmplitude stageFiveUpperThenLower
orderedStageFiveJoinsShareAmplitude = refl

orderedStageFiveJoinsDiffer :
  stageFiveLowerThenUpper ≡ stageFiveUpperThenLower → ⊥
orderedStageFiveJoinsDiffer ()

data SquareMove : Set where
  identityMove quarterTurn halfTurn threeQuarterTurn
    horizontalReflection verticalReflection
    mainDiagonalReflection antiDiagonalReflection : SquareMove

applySquareMove : SquareMove → Sym.SquareCarrier → Sym.SquareCarrier
applySquareMove identityMove (Sym.squareCarrier h v) =
  Sym.squareCarrier h v
applySquareMove quarterTurn (Sym.squareCarrier h v) =
  Sym.squareCarrier (Sym.flipC2 v) h
applySquareMove halfTurn (Sym.squareCarrier h v) =
  Sym.squareCarrier (Sym.flipC2 h) (Sym.flipC2 v)
applySquareMove threeQuarterTurn (Sym.squareCarrier h v) =
  Sym.squareCarrier v (Sym.flipC2 h)
applySquareMove horizontalReflection (Sym.squareCarrier h v) =
  Sym.squareCarrier h (Sym.flipC2 v)
applySquareMove verticalReflection (Sym.squareCarrier h v) =
  Sym.squareCarrier (Sym.flipC2 h) v
applySquareMove mainDiagonalReflection (Sym.squareCarrier h v) =
  Sym.squareCarrier v h
applySquareMove antiDiagonalReflection (Sym.squareCarrier h v) =
  Sym.squareCarrier (Sym.flipC2 v) (Sym.flipC2 h)

allSquareMoves : List SquareMove
allSquareMoves =
  identityMove ∷ quarterTurn ∷ halfTurn ∷ threeQuarterTurn
  ∷ horizontalReflection ∷ verticalReflection
  ∷ mainDiagonalReflection ∷ antiDiagonalReflection ∷ []

squareMoveCountIsEight : listCount allSquareMoves ≡ 8
squareMoveCountIsEight = refl

squareStateCountIsFour : Sym.squareCardinality ≡ 4
squareStateCountIsFour = Sym.squareCardinalityIsFour

record CounterpositionOrderedJoinBoundary : Set where
  constructor counterpositionOrderedJoinBoundary
  field
    binaryEmbeddingConstructed : Bool
    binaryEmbeddingConstructedIsTrue : binaryEmbeddingConstructed ≡ true
    counterpositionAlwaysFullInverse : Bool
    counterpositionAlwaysFullInverseIsFalse :
      counterpositionAlwaysFullInverse ≡ false
    counterpositionAlwaysDoubleInverse : Bool
    counterpositionAlwaysDoubleInverseIsFalse :
      counterpositionAlwaysDoubleInverse ≡ false
    externalIsOperatorAutomaticallyIdentified : Bool
    externalIsOperatorAutomaticallyIdentifiedIsFalse :
      externalIsOperatorAutomaticallyIdentified ≡ false
    equalAmplitudeErasesLowerUpperOrder : Bool
    equalAmplitudeErasesLowerUpperOrderIsFalse :
      equalAmplitudeErasesLowerUpperOrder ≡ false
    squareStateCarrierIdentifiedWithSquareMoveCarrier : Bool
    squareStateCarrierIdentifiedWithSquareMoveCarrierIsFalse :
      squareStateCarrierIdentifiedWithSquareMoveCarrier ≡ false

canonicalCounterpositionOrderedJoinBoundary :
  CounterpositionOrderedJoinBoundary
canonicalCounterpositionOrderedJoinBoundary =
  counterpositionOrderedJoinBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
