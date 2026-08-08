module DASHI.Foundations.BalancedTernaryAmplitudeClosureExact where

open import DASHI.Core.Prelude
open import DASHI.Core.Optional public

import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT

------------------------------------------------------------------------
-- The stage numeral is the signed amplitude of a retained line pattern.
-- Amplitude is a lossy projection: patterns, line order, frame, stabiliser,
-- and residual fibre remain part of the state.
------------------------------------------------------------------------

data Amplitude7 : Set where
  ampNeg3 ampNeg2 ampNeg1 ampZero ampPos1 ampPos2 ampPos3 : Amplitude7

amplitudeCode : Amplitude7 → Nat
amplitudeCode ampNeg3 = 0
amplitudeCode ampNeg2 = 1
amplitudeCode ampNeg1 = 2
amplitudeCode ampZero = 3
amplitudeCode ampPos1 = 4
amplitudeCode ampPos2 = 5
amplitudeCode ampPos3 = 6

triadAmplitude : BT.TriadPattern → Amplitude7
triadAmplitude (BT.triad BT.neg BT.neg BT.neg) = ampNeg3
triadAmplitude (BT.triad BT.neg BT.neg BT.zeroDigit) = ampNeg2
triadAmplitude (BT.triad BT.neg BT.neg BT.pos) = ampNeg1
triadAmplitude (BT.triad BT.neg BT.zeroDigit BT.neg) = ampNeg2
triadAmplitude (BT.triad BT.neg BT.zeroDigit BT.zeroDigit) = ampNeg1
triadAmplitude (BT.triad BT.neg BT.zeroDigit BT.pos) = ampZero
triadAmplitude (BT.triad BT.neg BT.pos BT.neg) = ampNeg1
triadAmplitude (BT.triad BT.neg BT.pos BT.zeroDigit) = ampZero
triadAmplitude (BT.triad BT.neg BT.pos BT.pos) = ampPos1
triadAmplitude (BT.triad BT.zeroDigit BT.neg BT.neg) = ampNeg2
triadAmplitude (BT.triad BT.zeroDigit BT.neg BT.zeroDigit) = ampNeg1
triadAmplitude (BT.triad BT.zeroDigit BT.neg BT.pos) = ampZero
triadAmplitude (BT.triad BT.zeroDigit BT.zeroDigit BT.neg) = ampNeg1
triadAmplitude (BT.triad BT.zeroDigit BT.zeroDigit BT.zeroDigit) = ampZero
triadAmplitude (BT.triad BT.zeroDigit BT.zeroDigit BT.pos) = ampPos1
triadAmplitude (BT.triad BT.zeroDigit BT.pos BT.neg) = ampZero
triadAmplitude (BT.triad BT.zeroDigit BT.pos BT.zeroDigit) = ampPos1
triadAmplitude (BT.triad BT.zeroDigit BT.pos BT.pos) = ampPos2
triadAmplitude (BT.triad BT.pos BT.neg BT.neg) = ampNeg1
triadAmplitude (BT.triad BT.pos BT.neg BT.zeroDigit) = ampZero
triadAmplitude (BT.triad BT.pos BT.neg BT.pos) = ampPos1
triadAmplitude (BT.triad BT.pos BT.zeroDigit BT.neg) = ampZero
triadAmplitude (BT.triad BT.pos BT.zeroDigit BT.zeroDigit) = ampPos1
triadAmplitude (BT.triad BT.pos BT.zeroDigit BT.pos) = ampPos2
triadAmplitude (BT.triad BT.pos BT.pos BT.neg) = ampPos1
triadAmplitude (BT.triad BT.pos BT.pos BT.zeroDigit) = ampPos2
triadAmplitude (BT.triad BT.pos BT.pos BT.pos) = ampPos3

allPositiveAmplitude : triadAmplitude BT.allPositive ≡ ampPos3
allPositiveAmplitude = refl

allNegativeAmplitude : triadAmplitude BT.allNegative ≡ ampNeg3
allNegativeAmplitude = refl

balancedZeroAmplitude : triadAmplitude BT.balancedZeroPattern ≡ ampZero
balancedZeroAmplitude = refl

twoPositiveOneOpenAmplitude :
  triadAmplitude BT.twoPositiveOneOpen ≡ ampPos2
twoPositiveOneOpenAmplitude = refl

------------------------------------------------------------------------
-- Two triads have a joined amplitude in {-6,...,+6}.  Encoding amplitude a
-- by a+3 turns signed addition into ordinary addition followed by decoding.
------------------------------------------------------------------------

data JoinedAmplitude13 : Set where
  joinedNeg6 joinedNeg5 joinedNeg4 joinedNeg3 joinedNeg2 joinedNeg1
    joinedZero
    joinedPos1 joinedPos2 joinedPos3 joinedPos4 joinedPos5 joinedPos6 :
    JoinedAmplitude13

decodeJoined : Nat → JoinedAmplitude13
decodeJoined zero = joinedNeg6
decodeJoined (suc zero) = joinedNeg5
decodeJoined (suc (suc zero)) = joinedNeg4
decodeJoined (suc (suc (suc zero))) = joinedNeg3
decodeJoined (suc (suc (suc (suc zero)))) = joinedNeg2
decodeJoined (suc (suc (suc (suc (suc zero))))) = joinedNeg1
decodeJoined (suc (suc (suc (suc (suc (suc zero)))))) = joinedZero
decodeJoined (suc (suc (suc (suc (suc (suc (suc zero))))))) = joinedPos1
decodeJoined (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = joinedPos2
decodeJoined (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = joinedPos3
decodeJoined (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) = joinedPos4
decodeJoined (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) = joinedPos5
decodeJoined _ = joinedPos6

joinAmplitude : BT.TriadPattern → BT.TriadPattern → JoinedAmplitude13
joinAmplitude left right =
  decodeJoined
    (amplitudeCode (triadAmplitude left) +
     amplitudeCode (triadAmplitude right))

sixJoinAmplitude :
  joinAmplitude BT.allPositive BT.allPositive ≡ joinedPos6
sixJoinAmplitude = refl

fiveJoinAmplitude :
  joinAmplitude BT.allPositive BT.twoPositiveOneOpen ≡ joinedPos5
fiveJoinAmplitude = refl

negativeSixJoinAmplitude :
  joinAmplitude BT.allNegative BT.allNegative ≡ joinedNeg6
negativeSixJoinAmplitude = refl

------------------------------------------------------------------------
-- Equal amplitudes do not determine equal patterns or unresolved coordinates.
------------------------------------------------------------------------

secondLineOpen : BT.TriadPattern
secondLineOpen = BT.triad BT.pos BT.zeroDigit BT.pos

firstLineOpen : BT.TriadPattern
firstLineOpen = BT.triad BT.zeroDigit BT.pos BT.pos

openPatternsShareAmplitude :
  triadAmplitude BT.twoPositiveOneOpen
  ≡ triadAmplitude secondLineOpen
  × triadAmplitude secondLineOpen
  ≡ triadAmplitude firstLineOpen
openPatternsShareAmplitude = refl , refl

thirdAndSecondOpenDiffer : BT.twoPositiveOneOpen ≡ secondLineOpen → ⊥
thirdAndSecondOpenDiffer ()

secondAndFirstOpenDiffer : secondLineOpen ≡ firstLineOpen → ⊥
secondAndFirstOpenDiffer ()

------------------------------------------------------------------------
-- Exact forward-remainder and closure-deficit profile for five.
------------------------------------------------------------------------

record ResidueDeficit369 : Set where
  constructor residueDeficit369
  field
    value : Nat
    quotient3 remainder3 : Nat
    quotientRemainder3 : 3 * quotient3 + remainder3 ≡ value
    deficit3 : Nat
    closesAtNext3 : value + deficit3 ≡ 6

    quotient6 remainder6 : Nat
    quotientRemainder6 : 6 * quotient6 + remainder6 ≡ value
    deficit6 : Nat
    closesAtNext6 : value + deficit6 ≡ 6

    quotient9 remainder9 : Nat
    quotientRemainder9 : 9 * quotient9 + remainder9 ≡ value
    deficit9 : Nat
    closesAtNext9 : value + deficit9 ≡ 9

open ResidueDeficit369 public

fiveResidueDeficitProfile : ResidueDeficit369
fiveResidueDeficitProfile =
  residueDeficit369
    5
    1 2 refl 1 refl
    0 5 refl 1 refl
    0 5 refl 4 refl

fiveHasTriadicOverflowTwo : remainder3 fiveResidueDeficitProfile ≡ 2
fiveHasTriadicOverflowTwo = refl

fiveIsOneShortOfSix : deficit6 fiveResidueDeficitProfile ≡ 1
fiveIsOneShortOfSix = refl

fiveIsFourShortOfNine : deficit9 fiveResidueDeficitProfile ≡ 4
fiveIsFourShortOfNine = refl

------------------------------------------------------------------------
-- Full Stage-5 constituent branching.  The existing visible 5 -> 3 edge is
-- one branch: withhold the incomplete sheet and retain it as residual.
------------------------------------------------------------------------

data StageFiveBranchKind : Set where
  positiveCompletion negativeResolution withholdIncomplete :
    StageFiveBranchKind

record StageFiveBranch : Set where
  constructor stageFiveBranch
  field
    kind : StageFiveBranchKind
    lowerBefore upperBefore : BT.TriadPattern
    upperAfter : BT.TriadPattern
    visibleTarget : Nat
    residual : Optional BT.TriadPattern
    upperAmplitudeAfter : Amplitude7
    upperAmplitudeExact : triadAmplitude upperAfter ≡ upperAmplitudeAfter
    upperStabiliserAfter : BT.StabiliserType
    upperStabiliserExact :
      BT.patternStabiliser upperAfter ≡ upperStabiliserAfter

open StageFiveBranch public

positiveStageFiveCompletion : StageFiveBranch
positiveStageFiveCompletion =
  stageFiveBranch
    positiveCompletion
    BT.allPositive BT.twoPositiveOneOpen BT.allPositive
    6 none ampPos3 refl BT.fullStabiliserS3 refl

negativeStageFiveResolution : StageFiveBranch
negativeStageFiveResolution =
  stageFiveBranch
    negativeResolution
    BT.allPositive BT.twoPositiveOneOpen BT.thirdCoordinateCounterposition
    4 none ampPos1 refl BT.pairStabiliserS2 refl

stageFiveFallbackWithResidual : StageFiveBranch
stageFiveFallbackWithResidual =
  stageFiveBranch
    withholdIncomplete
    BT.allPositive BT.twoPositiveOneOpen BT.twoPositiveOneOpen
    3 (some BT.twoPositiveOneOpen) ampPos2 refl BT.pairStabiliserS2 refl

positiveBranchRestoresS3 :
  upperStabiliserAfter positiveStageFiveCompletion ≡ BT.fullStabiliserS3
positiveBranchRestoresS3 = refl

negativeBranchRetainsS2 :
  upperStabiliserAfter negativeStageFiveResolution ≡ BT.pairStabiliserS2
negativeBranchRetainsS2 = refl

negativeBranchTargetsFour :
  visibleTarget negativeStageFiveResolution ≡ 4
negativeBranchTargetsFour = refl

fallbackTargetsThree : visibleTarget stageFiveFallbackWithResidual ≡ 3
fallbackTargetsThree = refl

fallbackRetainsUpperPattern :
  residual stageFiveFallbackWithResidual ≡ some BT.twoPositiveOneOpen
fallbackRetainsUpperPattern = refl

------------------------------------------------------------------------
-- Closure-profile arithmetic for stages 3 through 6.
------------------------------------------------------------------------

stageFourIsThreePlusOne : 3 + 1 ≡ 4
stageFourIsThreePlusOne = refl

stageFiveIsThreePlusTwo : 3 + 2 ≡ 5
stageFiveIsThreePlusTwo = refl

stageSixIsThreePlusThree : 3 + 3 ≡ 6
stageSixIsThreePlusThree = refl

record AmplitudeProjectionBoundary : Set where
  constructor amplitudeProjectionBoundary
  field
    amplitudeRangeConstructed : Bool
    amplitudeRangeConstructedIsTrue : amplitudeRangeConstructed ≡ true
    joinedAmplitudeRangeConstructed : Bool
    joinedAmplitudeRangeConstructedIsTrue :
      joinedAmplitudeRangeConstructed ≡ true
    amplitudeDeterminesLinePattern : Bool
    amplitudeDeterminesLinePatternIsFalse :
      amplitudeDeterminesLinePattern ≡ false
    fallbackErasesIncompleteSheet : Bool
    fallbackErasesIncompleteSheetIsFalse :
      fallbackErasesIncompleteSheet ≡ false
    irrepDecompositionGeneratesPrimaryFiveToThreeArithmetic : Bool
    irrepDecompositionGeneratesPrimaryFiveToThreeArithmeticIsFalse :
      irrepDecompositionGeneratesPrimaryFiveToThreeArithmetic ≡ false

canonicalAmplitudeProjectionBoundary : AmplitudeProjectionBoundary
canonicalAmplitudeProjectionBoundary =
  amplitudeProjectionBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
