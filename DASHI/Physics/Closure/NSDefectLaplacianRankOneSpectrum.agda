module DASHI.Physics.Closure.NSDefectLaplacianRankOneSpectrum where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Finite rank-one defect Laplacian spectrum surface.
--
-- This module records only the finite analytic sample
--
--   lambda_delta(alpha) = cos^2(alpha) sin^2(alpha).
--
-- The angle values are exact rational samples.  The denominator-sixteen
-- table records zero modes at radial/tangential states, positive middle
-- samples, and the maximum 1/4 at pi/4 as 4/16.  This is a checked finite
-- receipt, not a continuum Navier-Stokes regularity theorem and not a Clay
-- promotion.

data AngleState : Set where
  radialZero :
    AngleState
  shallowPiOverSix :
    AngleState
  balancedPiOverFour :
    AngleState
  steepPiOverThree :
    AngleState
  tangentialPiOverTwo :
    AngleState

allAngleStates : List AngleState
allAngleStates =
  radialZero
  ∷ shallowPiOverSix
  ∷ balancedPiOverFour
  ∷ steepPiOverThree
  ∷ tangentialPiOverTwo
  ∷ []

angleStateCount : Nat
angleStateCount = 5

lambdaDeltaDenominator16 : Nat
lambdaDeltaDenominator16 = 16

lambdaDeltaMaxDenominator4 : Nat
lambdaDeltaMaxDenominator4 = 4

lambdaDeltaNumerator16 : AngleState → Nat
lambdaDeltaNumerator16 radialZero =
  0
lambdaDeltaNumerator16 shallowPiOverSix =
  3
lambdaDeltaNumerator16 balancedPiOverFour =
  4
lambdaDeltaNumerator16 steepPiOverThree =
  3
lambdaDeltaNumerator16 tangentialPiOverTwo =
  0

cosSquaredNumerator4 : AngleState → Nat
cosSquaredNumerator4 radialZero =
  4
cosSquaredNumerator4 shallowPiOverSix =
  3
cosSquaredNumerator4 balancedPiOverFour =
  2
cosSquaredNumerator4 steepPiOverThree =
  1
cosSquaredNumerator4 tangentialPiOverTwo =
  0

sinSquaredNumerator4 : AngleState → Nat
sinSquaredNumerator4 radialZero =
  0
sinSquaredNumerator4 shallowPiOverSix =
  1
sinSquaredNumerator4 balancedPiOverFour =
  2
sinSquaredNumerator4 steepPiOverThree =
  3
sinSquaredNumerator4 tangentialPiOverTwo =
  4

lambdaDeltaProductNumerator16 : AngleState → Nat
lambdaDeltaProductNumerator16 state =
  cosSquaredNumerator4 state * sinSquaredNumerator4 state

lambdaDeltaFormulaHolds : (state : AngleState) →
  lambdaDeltaNumerator16 state ≡ lambdaDeltaProductNumerator16 state
lambdaDeltaFormulaHolds radialZero =
  refl
lambdaDeltaFormulaHolds shallowPiOverSix =
  refl
lambdaDeltaFormulaHolds balancedPiOverFour =
  refl
lambdaDeltaFormulaHolds steepPiOverThree =
  refl
lambdaDeltaFormulaHolds tangentialPiOverTwo =
  refl

zeroMode : AngleState → Bool
zeroMode radialZero =
  true
zeroMode shallowPiOverSix =
  false
zeroMode balancedPiOverFour =
  false
zeroMode steepPiOverThree =
  false
zeroMode tangentialPiOverTwo =
  true

radialOrTangential : AngleState → Bool
radialOrTangential radialZero =
  true
radialOrTangential shallowPiOverSix =
  false
radialOrTangential balancedPiOverFour =
  false
radialOrTangential steepPiOverThree =
  false
radialOrTangential tangentialPiOverTwo =
  true

zeroModeIffRadialTangential : (state : AngleState) →
  zeroMode state ≡ radialOrTangential state
zeroModeIffRadialTangential radialZero =
  refl
zeroModeIffRadialTangential shallowPiOverSix =
  refl
zeroModeIffRadialTangential balancedPiOverFour =
  refl
zeroModeIffRadialTangential steepPiOverThree =
  refl
zeroModeIffRadialTangential tangentialPiOverTwo =
  refl

maxWitness : AngleState
maxWitness =
  balancedPiOverFour

maxWitnessNumerator16 : Nat
maxWitnessNumerator16 =
  lambdaDeltaNumerator16 maxWitness

maxWitnessNumerator16Is4 : maxWitnessNumerator16 ≡ 4
maxWitnessNumerator16Is4 =
  refl

maxWitnessDenominator16Is16 : lambdaDeltaDenominator16 ≡ 16
maxWitnessDenominator16Is16 =
  refl

maxWitnessOneQuarterNumerator : Nat
maxWitnessOneQuarterNumerator =
  1

maxWitnessOneQuarterDenominator : Nat
maxWitnessOneQuarterDenominator =
  lambdaDeltaMaxDenominator4

maxWitnessOneQuarterEncoded : maxWitnessOneQuarterDenominator ≡ 4
maxWitnessOneQuarterEncoded =
  refl

offZeroPositive : AngleState → Bool
offZeroPositive radialZero =
  false
offZeroPositive shallowPiOverSix =
  true
offZeroPositive balancedPiOverFour =
  true
offZeroPositive steepPiOverThree =
  true
offZeroPositive tangentialPiOverTwo =
  false

offZeroPositiveShallow : offZeroPositive shallowPiOverSix ≡ true
offZeroPositiveShallow =
  refl

offZeroPositiveBalanced : offZeroPositive balancedPiOverFour ≡ true
offZeroPositiveBalanced =
  refl

offZeroPositiveSteep : offZeroPositive steepPiOverThree ≡ true
offZeroPositiveSteep =
  refl

zeroModeRadialNumeratorZero :
  lambdaDeltaNumerator16 radialZero ≡ 0
zeroModeRadialNumeratorZero =
  refl

zeroModeTangentialNumeratorZero :
  lambdaDeltaNumerator16 tangentialPiOverTwo ≡ 0
zeroModeTangentialNumeratorZero =
  refl

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

clayNavierStokesPromotedIsFalse :
  clayNavierStokesPromoted ≡ false
clayNavierStokesPromotedIsFalse =
  refl

fullClayNSSolved : Bool
fullClayNSSolved =
  false

fullClayNSSolvedIsFalse :
  fullClayNSSolved ≡ false
fullClayNSSolvedIsFalse =
  refl

data NSDefectLaplacianRankOnePromotion : Set where

nsDefectLaplacianRankOnePromotionImpossibleHere :
  NSDefectLaplacianRankOnePromotion →
  ⊥
nsDefectLaplacianRankOnePromotionImpossibleHere ()

data FiniteRankOneSpectrumStatus : Set where
  finiteRankOneSpectrumRecordedFailClosed :
    FiniteRankOneSpectrumStatus

rankOneDefectFormulaString : String
rankOneDefectFormulaString =
  "lambda_delta(alpha)=cos^2(alpha)sin^2(alpha); finite samples use denominator 16, with pi/4 maximum 4/16=1/4."

promotionGuardString : String
promotionGuardString =
  "clayNavierStokesPromoted=false; this finite rank-one defect Laplacian sample is not a Clay Navier-Stokes proof."

organizationString : String
organizationString =
  "O: Finite NS rank-one defect Laplacian spectrum surface over five AngleState samples."

requirementString : String
requirementString =
  "R: Encode lambda_delta=cos^2 alpha sin^2 alpha exactly on zero, middle, and pi/4 max samples while failing closed for Clay."

codeArtifactString : String
codeArtifactString =
  "C: DASHI.Physics.Closure.NSDefectLaplacianRankOneSpectrum exports AngleState, exact Nat numerators, zeroMode iff radial/tangential, maxWitness, offZeroPositive, and false Clay flags."

stateString : String
stateString =
  "S: lambda numerators over 16 are 0,3,4,3,0; zeroMode iff radial/tangential; off-zero middle samples positive; clayNavierStokesPromoted=false."

latticeString : String
latticeString =
  "L: finite angles -> cos^2/sin^2 rational table -> lambda product numerator -> zero/max/positive receipts -> fail-closed Clay boundary."

proposalString : String
proposalString =
  "P: Use this as a finite analytic receipt only; any continuum NS or Clay promotion must enter through a separate external theorem surface."

governanceString : String
governanceString =
  "G: Promotion type is empty and both fullClayNSSolved and clayNavierStokesPromoted remain false."

gapString : String
gapString =
  "F: Remaining gap is the entire continuum large-data Navier-Stokes regularity route; no such claim is made by the finite spectrum table."

record NSDefectLaplacianRankOneSpectrumReceipt : Set where
  field
    status :
      FiniteRankOneSpectrumStatus

    states :
      List AngleState

    statesAreCanonical :
      states ≡ allAngleStates

    denominator16 :
      Nat

    denominator16Is16 :
      denominator16 ≡ 16

    radialZeroNumerator :
      Nat

    radialZeroNumeratorIs0 :
      radialZeroNumerator ≡ 0

    shallowNumerator :
      Nat

    shallowNumeratorIs3 :
      shallowNumerator ≡ 3

    balancedNumerator :
      Nat

    balancedNumeratorIs4 :
      balancedNumerator ≡ 4

    steepNumerator :
      Nat

    steepNumeratorIs3 :
      steepNumerator ≡ 3

    tangentialNumerator :
      Nat

    tangentialNumeratorIs0 :
      tangentialNumerator ≡ 0

    zeroModeIffRadialTangentialReceipt :
      (state : AngleState) → zeroMode state ≡ radialOrTangential state

    maxWitnessReceipt :
      AngleState

    maxWitnessIsBalanced :
      maxWitnessReceipt ≡ balancedPiOverFour

    maxWitnessNumeratorIs4 :
      lambdaDeltaNumerator16 maxWitnessReceipt ≡ 4

    maxWitnessOneQuarterDenominatorIs4 :
      maxWitnessOneQuarterDenominator ≡ 4

    offZeroPositiveShallowReceipt :
      offZeroPositive shallowPiOverSix ≡ true

    offZeroPositiveBalancedReceipt :
      offZeroPositive balancedPiOverFour ≡ true

    offZeroPositiveSteepReceipt :
      offZeroPositive steepPiOverThree ≡ true

    lambdaFormulaReceipt :
      (state : AngleState) →
        lambdaDeltaNumerator16 state ≡ lambdaDeltaProductNumerator16 state

    clayNavierStokesPromotedReceipt :
      Bool

    clayNavierStokesPromotedReceiptIsFalse :
      clayNavierStokesPromotedReceipt ≡ false

    fullClayNSSolvedReceipt :
      Bool

    fullClayNSSolvedReceiptIsFalse :
      fullClayNSSolvedReceipt ≡ false

    formulaStatement :
      String

    formulaStatementIsCanonical :
      formulaStatement ≡ rankOneDefectFormulaString

    promotionGuard :
      String

    promotionGuardIsCanonical :
      promotionGuard ≡ promotionGuardString

open NSDefectLaplacianRankOneSpectrumReceipt public

canonicalNSDefectLaplacianRankOneSpectrumReceipt :
  NSDefectLaplacianRankOneSpectrumReceipt
canonicalNSDefectLaplacianRankOneSpectrumReceipt =
  record
    { status =
        finiteRankOneSpectrumRecordedFailClosed
    ; states =
        allAngleStates
    ; statesAreCanonical =
        refl
    ; denominator16 =
        lambdaDeltaDenominator16
    ; denominator16Is16 =
        refl
    ; radialZeroNumerator =
        lambdaDeltaNumerator16 radialZero
    ; radialZeroNumeratorIs0 =
        refl
    ; shallowNumerator =
        lambdaDeltaNumerator16 shallowPiOverSix
    ; shallowNumeratorIs3 =
        refl
    ; balancedNumerator =
        lambdaDeltaNumerator16 balancedPiOverFour
    ; balancedNumeratorIs4 =
        refl
    ; steepNumerator =
        lambdaDeltaNumerator16 steepPiOverThree
    ; steepNumeratorIs3 =
        refl
    ; tangentialNumerator =
        lambdaDeltaNumerator16 tangentialPiOverTwo
    ; tangentialNumeratorIs0 =
        refl
    ; zeroModeIffRadialTangentialReceipt =
        zeroModeIffRadialTangential
    ; maxWitnessReceipt =
        maxWitness
    ; maxWitnessIsBalanced =
        refl
    ; maxWitnessNumeratorIs4 =
        refl
    ; maxWitnessOneQuarterDenominatorIs4 =
        refl
    ; offZeroPositiveShallowReceipt =
        refl
    ; offZeroPositiveBalancedReceipt =
        refl
    ; offZeroPositiveSteepReceipt =
        refl
    ; lambdaFormulaReceipt =
        lambdaDeltaFormulaHolds
    ; clayNavierStokesPromotedReceipt =
        clayNavierStokesPromoted
    ; clayNavierStokesPromotedReceiptIsFalse =
        refl
    ; fullClayNSSolvedReceipt =
        fullClayNSSolved
    ; fullClayNSSolvedReceiptIsFalse =
        refl
    ; formulaStatement =
        rankOneDefectFormulaString
    ; formulaStatementIsCanonical =
        refl
    ; promotionGuard =
        promotionGuardString
    ; promotionGuardIsCanonical =
        refl
    }

canonicalReceiptKeepsClayFalse :
  clayNavierStokesPromotedReceipt
    canonicalNSDefectLaplacianRankOneSpectrumReceipt ≡ false
canonicalReceiptKeepsClayFalse =
  refl

canonicalReceiptMaxWitnessIsPiOverFour :
  maxWitnessReceipt
    canonicalNSDefectLaplacianRankOneSpectrumReceipt ≡ balancedPiOverFour
canonicalReceiptMaxWitnessIsPiOverFour =
  refl
