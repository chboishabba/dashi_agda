module DASHI.Biology.SignedSSPFRACTRANWeaveExact where

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.OrientedZeroWaveTransitionExact as Zero
import DASHI.Biology.ReducedFiftyThreeFibreExact as Reduced
import DASHI.Geometry.SSP369Ultrametric as SSP

------------------------------------------------------------------------
-- The complete fifteen SSP/Ogg lanes.  A lane is a typed symmetry/fibre
-- address; its prime value supplies FRACTRAN arithmetic, but the value alone
-- does not determine the fibre geometry or representation action.

data SSPPrime : Set where
  ssp2 : SSPPrime
  ssp3 : SSPPrime
  ssp5 : SSPPrime
  ssp7 : SSPPrime
  ssp11 : SSPPrime
  ssp13 : SSPPrime
  ssp17 : SSPPrime
  ssp19 : SSPPrime
  ssp23 : SSPPrime
  ssp29 : SSPPrime
  ssp31 : SSPPrime
  ssp41 : SSPPrime
  ssp47 : SSPPrime
  ssp59 : SSPPrime
  ssp71 : SSPPrime

primeValue : SSPPrime → Nat
primeValue ssp2 = 2
primeValue ssp3 = 3
primeValue ssp5 = 5
primeValue ssp7 = 7
primeValue ssp11 = 11
primeValue ssp13 = 13
primeValue ssp17 = 17
primeValue ssp19 = 19
primeValue ssp23 = 23
primeValue ssp29 = 29
primeValue ssp31 = 31
primeValue ssp41 = 41
primeValue ssp47 = 47
primeValue ssp59 = 59
primeValue ssp71 = 71

canonicalSSPPrimes : List SSPPrime
canonicalSSPPrimes =
  ssp2 ∷ ssp3 ∷ ssp5 ∷ ssp7 ∷ ssp11 ∷ ssp13 ∷ ssp17 ∷ ssp19
  ∷ ssp23 ∷ ssp29 ∷ ssp31 ∷ ssp41 ∷ ssp47 ∷ ssp59 ∷ ssp71 ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ xs) = suc (listCount xs)

canonicalSSPPrimeCountIsFifteen : listCount canonicalSSPPrimes ≡ 15
canonicalSSPPrimeCountIsFifteen = refl

-- Rank is structural order in the declared fifteen-lane SSP atlas, not a
-- theorem that numerical prime size alone measures physical complexity.
sspComplexityRank : SSPPrime → Nat
sspComplexityRank ssp2 = 0
sspComplexityRank ssp3 = 1
sspComplexityRank ssp5 = 2
sspComplexityRank ssp7 = 3
sspComplexityRank ssp11 = 4
sspComplexityRank ssp13 = 5
sspComplexityRank ssp17 = 6
sspComplexityRank ssp19 = 7
sspComplexityRank ssp23 = 8
sspComplexityRank ssp29 = 9
sspComplexityRank ssp31 = 10
sspComplexityRank ssp41 = 11
sspComplexityRank ssp47 = 12
sspComplexityRank ssp59 = 13
sspComplexityRank ssp71 = 14

largestThreeSSPRanksAreSuccessive :
  sspComplexityRank ssp47 ≡ 12
  × sspComplexityRank ssp59 ≡ 13
  × sspComplexityRank ssp71 ≡ 14
largestThreeSSPRanksAreSuccessive = refl , (refl , refl)

------------------------------------------------------------------------
-- Balanced/signed valuations.  Negative multiplicity is already native to
-- FRACTRAN denominators and to inverse fibre transport; coarse ternary sign
-- forgets magnitude while preserving polarity.

data SignedMultiplicity : Set where
  negativeMultiplicity : Nat → SignedMultiplicity
  zeroMultiplicity : SignedMultiplicity
  positiveMultiplicity : Nat → SignedMultiplicity

data FibreOrientation : Set where
  inverseOrientation : FibreOrientation
  mediatedOrientation : FibreOrientation
  forwardOrientation : FibreOrientation

orientationOfMultiplicity : SignedMultiplicity → FibreOrientation
orientationOfMultiplicity (negativeMultiplicity n) = inverseOrientation
orientationOfMultiplicity zeroMultiplicity = mediatedOrientation
orientationOfMultiplicity (positiveMultiplicity n) = forwardOrientation

negateMultiplicity : SignedMultiplicity → SignedMultiplicity
negateMultiplicity (negativeMultiplicity n) = positiveMultiplicity n
negateMultiplicity zeroMultiplicity = zeroMultiplicity
negateMultiplicity (positiveMultiplicity n) = negativeMultiplicity n

coarseMultiplicity : SignedMultiplicity → Triadic.KernelTrit
coarseMultiplicity (negativeMultiplicity n) = Triadic.negativeTrit
coarseMultiplicity zeroMultiplicity = Triadic.zeroTrit
coarseMultiplicity (positiveMultiplicity n) = Triadic.positiveTrit

SSPValuation : Set
SSPValuation = SSPPrime → SignedMultiplicity

zeroValuation : SSPValuation
zeroValuation prime = zeroMultiplicity

largeOggProductValuation : SSPValuation
largeOggProductValuation ssp47 = positiveMultiplicity 1
largeOggProductValuation ssp59 = positiveMultiplicity 1
largeOggProductValuation ssp71 = positiveMultiplicity 1
largeOggProductValuation prime = zeroMultiplicity

virtualFiftyThreeValuation : SSPValuation
virtualFiftyThreeValuation ssp59 = positiveMultiplicity 1
virtualFiftyThreeValuation ssp7 = negativeMultiplicity 1
virtualFiftyThreeValuation prime = zeroMultiplicity

largeOggValuationAtFortySeven :
  largeOggProductValuation ssp47 ≡ positiveMultiplicity 1
largeOggValuationAtFortySeven = refl

largeOggValuationAtFiftyNine :
  largeOggProductValuation ssp59 ≡ positiveMultiplicity 1
largeOggValuationAtFiftyNine = refl

largeOggValuationAtSeventyOne :
  largeOggProductValuation ssp71 ≡ positiveMultiplicity 1
largeOggValuationAtSeventyOne = refl

virtualFiftyThreeHasPositiveFiftyNine :
  virtualFiftyThreeValuation ssp59 ≡ positiveMultiplicity 1
virtualFiftyThreeHasPositiveFiftyNine = refl

virtualFiftyThreeHasNegativeSeven :
  virtualFiftyThreeValuation ssp7 ≡ negativeMultiplicity 1
virtualFiftyThreeHasNegativeSeven = refl

------------------------------------------------------------------------
-- Exact additive/virtual SSP presentations of 53.  The equations are written
-- without integer subtraction so they remain constructive Nat equalities.

fiftyThreeAsFortySevenPlusFivePlusUnit : 47 + 5 + 1 ≡ 53
fiftyThreeAsFortySevenPlusFivePlusUnit = refl

fiftyThreeAsFiftyNineMinusSevenPlusUnit : 59 + 1 ≡ 53 + 7
fiftyThreeAsFiftyNineMinusSevenPlusUnit = refl

fiftyThreeAsSeventyOneMinusNineteenPlusUnit : 71 + 1 ≡ 53 + 19
fiftyThreeAsSeventyOneMinusNineteenPlusUnit = refl

fiftyThreeAsReducedSixByNine : Reduced.fullSixByNineDimension ∸ 1 ≡ 53
fiftyThreeAsReducedSixByNine = refl

------------------------------------------------------------------------
-- Canonicality is geometric first: 54 - 1 is a one-step reduced-fibre
-- construction.  Alternative SSP arithmetic words remain valid compilation
-- views but have a larger declared normal-form cost in this finite candidate
-- family.

data FiftyThreePresentation : Set where
  reducedSixByNineMinusInvariant : FiftyThreePresentation
  positiveFortySevenFiveUnit : FiftyThreePresentation
  virtualFiftyNineSevenUnit : FiftyThreePresentation
  virtualSeventyOneNineteenUnit : FiftyThreePresentation

presentationCost : FiftyThreePresentation → Nat
presentationCost reducedSixByNineMinusInvariant = 1
presentationCost positiveFortySevenFiveUnit = 3
presentationCost virtualFiftyNineSevenUnit = 3
presentationCost virtualSeventyOneNineteenUnit = 3

canonicalFiftyThreePresentation : FiftyThreePresentation
canonicalFiftyThreePresentation = reducedSixByNineMinusInvariant

canonicalPresentationIsCostMinimal :
  (presentation : FiftyThreePresentation) →
  presentationCost canonicalFiftyThreePresentation
  ≤ presentationCost presentation
canonicalPresentationIsCostMinimal reducedSixByNineMinusInvariant = s≤s z≤n
canonicalPresentationIsCostMinimal positiveFortySevenFiveUnit = s≤s z≤n
canonicalPresentationIsCostMinimal virtualFiftyNineSevenUnit = s≤s z≤n
canonicalPresentationIsCostMinimal virtualSeventyOneNineteenUnit = s≤s z≤n

------------------------------------------------------------------------
-- FRACTRAN weave instructions distinguish program description, execution
-- length, normal form, and retained residual witnesses.

data WeaveInstruction : Set where
  buildSixByNineFibre : WeaveInstruction
  removeInvariantMode : WeaveInstruction
  introducePrime : SSPPrime → WeaveInstruction
  introduceInversePrime : SSPPrime → WeaveInstruction
  introduceInvariantUnit : WeaveInstruction
  refineAt369 : WeaveInstruction

canonicalGeometricFiftyThreeProgram : List WeaveInstruction
canonicalGeometricFiftyThreeProgram =
  buildSixByNineFibre ∷ removeInvariantMode ∷ []

canonicalVirtualFiftyThreeProgram : List WeaveInstruction
canonicalVirtualFiftyThreeProgram =
  introducePrime ssp59
  ∷ introduceInversePrime ssp7
  ∷ introduceInvariantUnit
  ∷ []

geometricProgramLengthIsTwo :
  listCount canonicalGeometricFiftyThreeProgram ≡ 2
geometricProgramLengthIsTwo = refl

virtualProgramLengthIsThree :
  listCount canonicalVirtualFiftyThreeProgram ≡ 3
virtualProgramLengthIsThree = refl

record WeaveEffect : Set where
  constructor weaveEffect
  field
    builtSites : Nat
    removedInvariantModes : Nat
    positivePrimeTokens : Nat
    inversePrimeTokens : Nat
    invariantTokens : Nat
    refinementSteps : Nat

open WeaveEffect public

emptyWeaveEffect : WeaveEffect
emptyWeaveEffect = weaveEffect 0 0 0 0 0 0

applyInstruction : WeaveInstruction → WeaveEffect → WeaveEffect
applyInstruction buildSixByNineFibre
  (weaveEffect sites removed positive inverse units refined) =
  weaveEffect (sites + 54) removed positive inverse units refined
applyInstruction removeInvariantMode
  (weaveEffect sites removed positive inverse units refined) =
  weaveEffect sites (suc removed) positive inverse units refined
applyInstruction (introducePrime prime)
  (weaveEffect sites removed positive inverse units refined) =
  weaveEffect sites removed (suc positive) inverse units refined
applyInstruction (introduceInversePrime prime)
  (weaveEffect sites removed positive inverse units refined) =
  weaveEffect sites removed positive (suc inverse) units refined
applyInstruction introduceInvariantUnit
  (weaveEffect sites removed positive inverse units refined) =
  weaveEffect sites removed positive inverse (suc units) refined
applyInstruction refineAt369
  (weaveEffect sites removed positive inverse units refined) =
  weaveEffect sites removed positive inverse units (suc refined)

executeProgram : List WeaveInstruction → WeaveEffect → WeaveEffect
executeProgram [] effect = effect
executeProgram (instruction ∷ program) effect =
  executeProgram program (applyInstruction instruction effect)

canonicalGeometricProgramEffect : WeaveEffect
canonicalGeometricProgramEffect =
  executeProgram canonicalGeometricFiftyThreeProgram emptyWeaveEffect

canonicalGeometricProgramBuildsFiftyFourAndRemovesOne :
  builtSites canonicalGeometricProgramEffect ≡ 54
  × removedInvariantModes canonicalGeometricProgramEffect ≡ 1
canonicalGeometricProgramBuildsFiftyFourAndRemovesOne = refl , refl

canonicalVirtualProgramEffect : WeaveEffect
canonicalVirtualProgramEffect =
  executeProgram canonicalVirtualFiftyThreeProgram emptyWeaveEffect

canonicalVirtualProgramHasOnePositiveOneInverseOneUnit :
  positivePrimeTokens canonicalVirtualProgramEffect ≡ 1
  × inversePrimeTokens canonicalVirtualProgramEffect ≡ 1
  × invariantTokens canonicalVirtualProgramEffect ≡ 1
canonicalVirtualProgramHasOnePositiveOneInverseOneUnit =
  refl , (refl , refl)

canonicalSSPAddress : SSP.Address 3
canonicalSSPAddress =
  SSP.digit3 vcons SSP.digit6 vcons SSP.digit9 vcons vnil

record SSPHyperformLane : Set where
  constructor sspHyperformLane
  field
    primeLane : SSPPrime
    declaredComplexityRank : Nat
    rankCertificate : declaredComplexityRank ≡ sspComplexityRank primeLane
    address : SSP.Address 3
    orientation : FibreOrientation

open SSPHyperformLane public

canonicalFortySevenForwardLane : SSPHyperformLane
canonicalFortySevenForwardLane =
  sspHyperformLane ssp47 12 refl canonicalSSPAddress forwardOrientation

canonicalSevenInverseLane : SSPHyperformLane
canonicalSevenInverseLane =
  sspHyperformLane ssp7 3 refl canonicalSSPAddress inverseOrientation

record SignedSSPExecutionState : Set where
  constructor signedSSPExecutionState
  field
    valuation : SSPValuation
    invariantUnits : Nat
    address369 : SSP.Address 3
    zeroApproachResidual : Zero.ApproachDirection
    programLength : Nat
    executionLength : Nat
    normalFormLength : Nat
    residualWitnessLength : Nat

open SignedSSPExecutionState public

canonicalVirtualFiftyThreeState : SignedSSPExecutionState
canonicalVirtualFiftyThreeState =
  signedSSPExecutionState
    virtualFiftyThreeValuation
    1
    canonicalSSPAddress
    Zero.fromNegative
    3
    3
    3
    1

canonicalGeometryFiftyThreeState : SignedSSPExecutionState
canonicalGeometryFiftyThreeState =
  signedSSPExecutionState
    zeroValuation
    0
    canonicalSSPAddress
    Zero.stationaryAtZero
    2
    54
    2
    1

typedDescriptionLength : SignedSSPExecutionState → Nat
typedDescriptionLength state =
  programLength state
  + normalFormLength state
  + residualWitnessLength state

canonicalGeometryTypedDescriptionLengthIsFive :
  typedDescriptionLength canonicalGeometryFiftyThreeState ≡ 5
canonicalGeometryTypedDescriptionLengthIsFive = refl

canonicalGeometryExecutionLengthIsFiftyFour :
  executionLength canonicalGeometryFiftyThreeState ≡ 54
canonicalGeometryExecutionLengthIsFiftyFour = refl

record SignedSSPWeaveBoundary : Set where
  constructor signedSSPWeaveBoundary
  field
    negativeSSPRequiresNewNonFRACTRANSemantics : Bool
    negativeSSPRequiresNewNonFRACTRANSemanticsIsFalse :
      negativeSSPRequiresNewNonFRACTRANSemantics ≡ false

    shortestProgramLengthEqualsExecutionLength : Bool
    shortestProgramLengthEqualsExecutionLengthIsFalse :
      shortestProgramLengthEqualsExecutionLength ≡ false

    finiteCostSelectionIsKolmogorovComplexityTheorem : Bool
    finiteCostSelectionIsKolmogorovComplexityTheoremIsFalse :
      finiteCostSelectionIsKolmogorovComplexityTheorem ≡ false

    fiftyThreeMustBeAnIndependentPrimeValuation : Bool
    fiftyThreeMustBeAnIndependentPrimeValuationIsFalse :
      fiftyThreeMustBeAnIndependentPrimeValuation ≡ false

open SignedSSPWeaveBoundary public

canonicalSignedSSPWeaveBoundary : SignedSSPWeaveBoundary
canonicalSignedSSPWeaveBoundary =
  signedSSPWeaveBoundary false refl false refl false refl false refl
