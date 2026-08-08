module DASHI.Foundations.BalancedTernaryStageSymmetryExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Balanced ternary is retained as a structured carrier.  Its amplitude is a
-- projection and never replaces the line pattern, constituent decomposition,
-- symmetry type, or unresolved fibre.
------------------------------------------------------------------------

data BalancedDigit : Set where
  neg zeroDigit pos : BalancedDigit

record TriadPattern : Set where
  constructor triad
  field
    first second third : BalancedDigit

open TriadPattern public

allPositive : TriadPattern
allPositive = triad pos pos pos

twoPositiveOneOpen : TriadPattern
twoPositiveOneOpen = triad pos pos zeroDigit

balancedZeroPattern : TriadPattern
balancedZeroPattern = triad pos neg zeroDigit

allNegative : TriadPattern
allNegative = triad neg neg neg

countPositiveDigit : BalancedDigit → Nat
countPositiveDigit neg = 0
countPositiveDigit zeroDigit = 0
countPositiveDigit pos = 1

countNegativeDigit : BalancedDigit → Nat
countNegativeDigit neg = 1
countNegativeDigit zeroDigit = 0
countNegativeDigit pos = 0

record SignedBalance : Set where
  constructor signedBalance
  field
    positiveUnits negativeUnits : Nat

open SignedBalance public

patternBalance : TriadPattern → SignedBalance
patternBalance x =
  signedBalance
    (countPositiveDigit (first x) +
     countPositiveDigit (second x) +
     countPositiveDigit (third x))
    (countNegativeDigit (first x) +
     countNegativeDigit (second x) +
     countNegativeDigit (third x))

allPositiveBalance : patternBalance allPositive ≡ signedBalance 3 0
allPositiveBalance = refl

twoPositiveOneOpenBalance :
  patternBalance twoPositiveOneOpen ≡ signedBalance 2 0
twoPositiveOneOpenBalance = refl

balancedZeroBalance :
  patternBalance balancedZeroPattern ≡ signedBalance 1 1
balancedZeroBalance = refl

allNegativeBalance : patternBalance allNegative ≡ signedBalance 0 3
allNegativeBalance = refl

------------------------------------------------------------------------
-- Balanced/unbalanced carry identities.  Subtraction is expressed without
-- truncated natural subtraction: a = b-c is represented by a+c=b.
------------------------------------------------------------------------

twoIsThreeMinusOne : 2 + 1 ≡ 3
twoIsThreeMinusOne = refl

fiveIsThreePlusTwo : 3 + 2 ≡ 5
fiveIsThreePlusTwo = refl

fiveIsSixMinusOne : 5 + 1 ≡ 6
fiveIsSixMinusOne = refl

fiveIsNineMinusThreeMinusOne : 5 + 3 + 1 ≡ 9
fiveIsNineMinusThreeMinusOne = refl

sixIsTwoTimesThree : 2 * 3 ≡ 6
sixIsTwoTimesThree = refl

sixIsNineMinusThree : 6 + 3 ≡ 9
sixIsNineMinusThree = refl

nineIsThreeSquared : 3 ^ 2 ≡ 9
nineIsThreeSquared = refl

------------------------------------------------------------------------
-- Stage 5 is (+++) dot (++0), not the scalar five alone.  The 5 -> 3 edge is
-- a coarse retraction which retains the second constituent as a residual fibre.
------------------------------------------------------------------------

record TwoTriadComposite : Set where
  constructor twoTriadComposite
  field
    lower upper : TriadPattern
    lowerAmplitude upperAmplitude totalAmplitude : Nat
    lowerAmplitudeExact : lowerAmplitude ≡ 3
    upperAmplitudeExact : upperAmplitude ≡ 2
    totalExact : lowerAmplitude + upperAmplitude ≡ totalAmplitude

open TwoTriadComposite public

stage5Composite : TwoTriadComposite
stage5Composite =
  twoTriadComposite allPositive twoPositiveOneOpen 3 2 5 refl refl refl

record RetainedTriadicFallback : Set where
  constructor retainedTriadicFallback
  field
    original : TwoTriadComposite
    visibleClosedPattern : TriadPattern
    retainedResidualPattern : TriadPattern
    visibleAmplitude : Nat
    residualAmplitude : Nat
    visibleIsLower : visibleClosedPattern ≡ lower original
    residualIsUpper : retainedResidualPattern ≡ upper original
    visibleIsThree : visibleAmplitude ≡ 3
    residualIsTwo : residualAmplitude ≡ 2
    residualErased : Bool
    residualErasedIsFalse : residualErased ≡ false

open RetainedTriadicFallback public

stage5To3RetainsTwo : RetainedTriadicFallback
stage5To3RetainsTwo =
  retainedTriadicFallback
    stage5Composite allPositive twoPositiveOneOpen 3 2
    refl refl refl refl false refl

------------------------------------------------------------------------
-- Pattern symmetry is separate from amplitude.
------------------------------------------------------------------------

data StabiliserType : Set where
  trivialStabiliser : StabiliserType
  pairStabiliserS2 : StabiliserType
  fullStabiliserS3 : StabiliserType

patternStabiliser : TriadPattern → StabiliserType
patternStabiliser (triad pos pos pos) = fullStabiliserS3
patternStabiliser (triad neg neg neg) = fullStabiliserS3
patternStabiliser (triad pos pos zeroDigit) = pairStabiliserS2
patternStabiliser (triad pos zeroDigit pos) = pairStabiliserS2
patternStabiliser (triad zeroDigit pos pos) = pairStabiliserS2
patternStabiliser (triad neg neg zeroDigit) = pairStabiliserS2
patternStabiliser (triad neg zeroDigit neg) = pairStabiliserS2
patternStabiliser (triad zeroDigit neg neg) = pairStabiliserS2
patternStabiliser _ = trivialStabiliser

stage3PatternHasS3 : patternStabiliser allPositive ≡ fullStabiliserS3
stage3PatternHasS3 = refl

stage2PatternHasS2 :
  patternStabiliser twoPositiveOneOpen ≡ pairStabiliserS2
stage2PatternHasS2 = refl

record SymmetryAwareStageState : Set where
  constructor symmetryAwareStageState
  field
    linePattern : TriadPattern
    balance : SignedBalance
    stabiliser : StabiliserType
    balanceExact : balance ≡ patternBalance linePattern
    stabiliserExact : stabiliser ≡ patternStabiliser linePattern

stage3SymmetryState : SymmetryAwareStageState
stage3SymmetryState =
  symmetryAwareStageState allPositive (signedBalance 3 0)
    fullStabiliserS3 refl refl

stage2SymmetryState : SymmetryAwareStageState
stage2SymmetryState =
  symmetryAwareStageState twoPositiveOneOpen (signedBalance 2 0)
    pairStabiliserS2 refl refl

------------------------------------------------------------------------
-- Counterposition is context-indexed.  Strict inversion is one possible
-- counterposition, but a one-coordinate counterposition need not equal it.
------------------------------------------------------------------------

invertDigit : BalancedDigit → BalancedDigit
invertDigit neg = pos
invertDigit zeroDigit = zeroDigit
invertDigit pos = neg

strictInverse : TriadPattern → TriadPattern
strictInverse x =
  triad (invertDigit (first x))
        (invertDigit (second x))
        (invertDigit (third x))

thirdCoordinateCounterposition : TriadPattern
thirdCoordinateCounterposition = triad pos pos neg

allPositiveStrictInverse : strictInverse allPositive ≡ allNegative
allPositiveStrictInverse = refl

counterpositionNeedNotBeInverse :
  thirdCoordinateCounterposition ≡ strictInverse allPositive → ⊥
counterpositionNeedNotBeInverse ()

record CounterpositionWitness : Set where
  constructor counterpositionWitness
  field
    position counterposition : TriadPattern
    strictInverseClaimed : Bool
    strictInverseClaimedIsFalse : strictInverseClaimed ≡ false

partialCounterpositionWitness : CounterpositionWitness
partialCounterpositionWitness =
  counterpositionWitness allPositive thirdCoordinateCounterposition false refl

------------------------------------------------------------------------
-- Simultaneous 3/6/9 closure charts.
------------------------------------------------------------------------

record ClosureProfile369 : Set where
  constructor closureProfile369
  field
    value : Nat
    completedTriads triadicRemainder : Nat
    triadicDecomposition :
      3 * completedTriads + triadicRemainder ≡ value
    distanceToSix : Nat
    closesAtSix : value + distanceToSix ≡ 6
    distanceToNine : Nat
    closesAtNine : value + distanceToNine ≡ 9

fiveClosureProfile : ClosureProfile369
fiveClosureProfile = closureProfile369 5 1 2 refl 1 refl 4 refl

sixClosureProfile : ClosureProfile369
sixClosureProfile = closureProfile369 6 2 0 refl 0 refl 3 refl

------------------------------------------------------------------------
-- Balanced-ternary addresses form a retained radix tree.
------------------------------------------------------------------------

appendDigits : List BalancedDigit → List BalancedDigit → List BalancedDigit
appendDigits [] ys = ys
appendDigits (x ∷ xs) ys = x ∷ appendDigits xs ys

record BalancedTernaryAddress : Set where
  constructor balancedTernaryAddress
  field
    digitsHighToLow : List BalancedDigit
    representedValue : Nat
    balancingDebt : Nat
    promotedWeight : Nat
    denominatorClearedEquation :
      representedValue + balancingDebt ≡ promotedWeight

fiveBalancedAddress : BalancedTernaryAddress
fiveBalancedAddress =
  balancedTernaryAddress (pos ∷ neg ∷ neg ∷ []) 5 4 9 refl

sixBalancedAddress : BalancedTernaryAddress
sixBalancedAddress =
  balancedTernaryAddress (pos ∷ neg ∷ zeroDigit ∷ []) 6 3 9 refl

record SharedPrefixWitness
  (left right : BalancedTernaryAddress) : Set where
  constructor sharedPrefixWitness
  field
    prefix leftSuffix rightSuffix : List BalancedDigit
    leftDecomposition :
      appendDigits prefix leftSuffix ≡
      BalancedTernaryAddress.digitsHighToLow left
    rightDecomposition :
      appendDigits prefix rightSuffix ≡
      BalancedTernaryAddress.digitsHighToLow right
    prefixDepth : Nat

fiveSixSharedPrefix :
  SharedPrefixWitness fiveBalancedAddress sixBalancedAddress
fiveSixSharedPrefix =
  sharedPrefixWitness
    (pos ∷ neg ∷ []) (neg ∷ []) (zeroDigit ∷ []) refl refl 2

------------------------------------------------------------------------
-- Exact arithmetic candidates retained at the foundation boundary.  Domain-
-- specific Ogg/SSP interpretation is supplied by a downstream bridge.
------------------------------------------------------------------------

depthTwoNonaryIsEightyOne : 9 ^ 2 ≡ 81
depthTwoNonaryIsEightyOne = refl

eightyOneSplitsTenAndSeventyOne : 10 + 71 ≡ 81
eightyOneSplitsTenAndSeventyOne = refl

moonshineCoefficientDepthTwoEquation :
  2430 * 81 + 54 ≡ 196884
moonshineCoefficientDepthTwoEquation = refl

monsterConstituentDepthTwoEquation :
  2430 * 81 + 53 ≡ 196883
monsterConstituentDepthTwoEquation = refl

fiftyFourIsSixTimesNine : 6 * 9 ≡ 54
fiftyFourIsSixTimesNine = refl

fiftyThreePlusOneIsFiftyFour : 53 + 1 ≡ 54
fiftyThreePlusOneIsFiftyFour = refl

record DepthTwoResidueAuthorityBoundary : Set where
  constructor depthTwoResidueAuthorityBoundary
  field
    residueEquationExact : Bool
    residueEquationExactIsTrue : residueEquationExact ≡ true
    independentEvidenceForTenTimesThreePowerNine : Bool
    independentEvidenceForTenTimesThreePowerNineIsFalse :
      independentEvidenceForTenTimesThreePowerNine ≡ false
    canonicalEightyOneBlockModuleConstructed : Bool
    canonicalEightyOneBlockModuleConstructedIsFalse :
      canonicalEightyOneBlockModuleConstructed ≡ false

canonicalDepthTwoResidueAuthorityBoundary :
  DepthTwoResidueAuthorityBoundary
canonicalDepthTwoResidueAuthorityBoundary =
  depthTwoResidueAuthorityBoundary true refl false refl false refl
