module DASHI.Physics.QuantumVacuum.CasimirBrownMaclayEnergyConditionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Foundations.RecursiveRadixHypervoxel as HyperBase
import DASHI.Physics.Closure.SU2SO3369HypervoxelBridge as SO3
import DASHI.Physics.QuantumVacuum.BrownMaclayParallelPlateSourceAuthorityExact as BrownMaclay
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Kernel
import DASHI.Physics.QuantumVacuum.PhysicalQuantities as Q
import DASHI.Physics.QuantumVacuum.CasimirSO3StressContractionMaxCutExact as Stress

------------------------------------------------------------------------
-- BROWN-MACLAY PARALLEL-PLATE STRESS -> LOCAL ENERGY CONDITIONS
------------------------------------------------------------------------

normalizedEnergyDensity : ℚ
normalizedEnergyDensity = - 1ℚ

brownMaclayNormalizedSpatialStress : Stress.SpatialStressSheet ℚ
brownMaclayNormalizedSpatialStress
  (HyperBase.axis-low , HyperBase.axis-low) = 1ℚ
brownMaclayNormalizedSpatialStress
  (HyperBase.axis-low , HyperBase.axis-mid) = 0ℚ
brownMaclayNormalizedSpatialStress
  (HyperBase.axis-low , HyperBase.axis-high) = 0ℚ
brownMaclayNormalizedSpatialStress
  (HyperBase.axis-mid , HyperBase.axis-low) = 0ℚ
brownMaclayNormalizedSpatialStress
  (HyperBase.axis-mid , HyperBase.axis-mid) = 1ℚ
brownMaclayNormalizedSpatialStress
  (HyperBase.axis-mid , HyperBase.axis-high) = 0ℚ
brownMaclayNormalizedSpatialStress
  (HyperBase.axis-high , HyperBase.axis-low) = 0ℚ
brownMaclayNormalizedSpatialStress
  (HyperBase.axis-high , HyperBase.axis-mid) = 0ℚ
brownMaclayNormalizedSpatialStress
  (HyperBase.axis-high , HyperBase.axis-high) = - (Int.+ 3 / 1)

tangentOnePressureIsPlusOne :
  brownMaclayNormalizedSpatialStress
    (Stress.plateTangentOneAxis , Stress.plateTangentOneAxis)
  ≡ 1ℚ
tangentOnePressureIsPlusOne = refl

tangentTwoPressureIsPlusOne :
  brownMaclayNormalizedSpatialStress
    (Stress.plateTangentTwoAxis , Stress.plateTangentTwoAxis)
  ≡ 1ℚ
tangentTwoPressureIsPlusOne = refl

normalPressureIsMinusThree :
  Stress.normalPressure brownMaclayNormalizedSpatialStress
  ≡ - (Int.+ 3 / 1)
normalPressureIsMinusThree = refl

tangentOneNormalTractionVanishes :
  Stress.tractionAgainstPlateNormal
    brownMaclayNormalizedSpatialStress
    Stress.plateTangentOneAxis
  ≡ 0ℚ
tangentOneNormalTractionVanishes = refl

tangentTwoNormalTractionVanishes :
  Stress.tractionAgainstPlateNormal
    brownMaclayNormalizedSpatialStress
    Stress.plateTangentTwoAxis
  ≡ 0ℚ
tangentTwoNormalTractionVanishes = refl

------------------------------------------------------------------------
-- Exact local energy-condition combinations.
------------------------------------------------------------------------

tangentNullCombination : ℚ
tangentNullCombination =
  normalizedEnergyDensity
  + brownMaclayNormalizedSpatialStress
      (Stress.plateTangentOneAxis , Stress.plateTangentOneAxis)

normalNullCombination : ℚ
normalNullCombination =
  normalizedEnergyDensity
  + Stress.normalPressure brownMaclayNormalizedSpatialStress

activeStressCombination : ℚ
activeStressCombination =
  normalizedEnergyDensity
  + brownMaclayNormalizedSpatialStress
      (Stress.plateTangentOneAxis , Stress.plateTangentOneAxis)
  + brownMaclayNormalizedSpatialStress
      (Stress.plateTangentTwoAxis , Stress.plateTangentTwoAxis)
  + Stress.normalPressure brownMaclayNormalizedSpatialStress

-- Four-dimensional electromagnetic stress is traceless.  In the chosen
-- orthonormal sign convention this is -rho + p1 + p2 + pn = 0.
lorentzTraceCombination : ℚ
lorentzTraceCombination =
  (- normalizedEnergyDensity)
  + brownMaclayNormalizedSpatialStress
      (Stress.plateTangentOneAxis , Stress.plateTangentOneAxis)
  + brownMaclayNormalizedSpatialStress
      (Stress.plateTangentTwoAxis , Stress.plateTangentTwoAxis)
  + Stress.normalPressure brownMaclayNormalizedSpatialStress

tangentNullCombinationIsZero :
  tangentNullCombination ≡ 0ℚ
tangentNullCombinationIsZero = solve []

normalNullCombinationIsNegativeFour :
  normalNullCombination ≡ - (Int.+ 4 / 1)
normalNullCombinationIsNegativeFour = solve []

activeStressCombinationIsNegativeTwo :
  activeStressCombination ≡ - (Int.+ 2 / 1)
activeStressCombinationIsNegativeTwo = solve []

lorentzTraceCombinationIsZero :
  lorentzTraceCombination ≡ 0ℚ
lorentzTraceCombinationIsZero = solve []

------------------------------------------------------------------------
-- Arbitrary null direction.
--
-- Let normalWeight denote n_perp^2 for a unit spatial direction.  The two
-- tangential squared components then sum to 1-normalWeight.  Substitution into
-- rho + sum_i p_i n_i^2 gives exactly -4 normalWeight on the normalized scale.
-- Positivity/nonzero of normalWeight is an order-theoretic input, not inferred
-- from bare rational algebra here.
------------------------------------------------------------------------

normalizedNullContractionFromNormalWeight : ℚ → ℚ
normalizedNullContractionFromNormalWeight normalWeight =
  normalizedEnergyDensity
  + (1ℚ + (- normalWeight))
  + ((- (Int.+ 3 / 1)) * normalWeight)

nullContractionIsNegativeFourTimesNormalWeight :
  (normalWeight : ℚ) →
  normalizedNullContractionFromNormalWeight normalWeight
  ≡ - ((Int.+ 4 / 1) * normalWeight)
nullContractionIsNegativeFourTimesNormalWeight normalWeight = solve []

------------------------------------------------------------------------
-- Direction-sensitive condition verdicts.
------------------------------------------------------------------------

data LocalEnergyConditionVerdict : Set where
  conditionSatisfied : LocalEnergyConditionVerdict
  conditionSaturated : LocalEnergyConditionVerdict
  conditionViolated : LocalEnergyConditionVerdict

directionalNEC : Stress.PlateDirection → LocalEnergyConditionVerdict
directionalNEC Stress.tangentOne = conditionSaturated
directionalNEC Stress.tangentTwo = conditionSaturated
directionalNEC Stress.normal = conditionViolated

casimirNEC : LocalEnergyConditionVerdict
casimirNEC = conditionViolated

casimirWEC : LocalEnergyConditionVerdict
casimirWEC = conditionViolated

casimirSEC : LocalEnergyConditionVerdict
casimirSEC = conditionViolated

casimirDEC : LocalEnergyConditionVerdict
casimirDEC = conditionViolated

normalNECViolationWitness :
  directionalNEC Stress.normal ≡ conditionViolated
normalNECViolationWitness = refl

tangentOneNECSaturationWitness :
  directionalNEC Stress.tangentOne ≡ conditionSaturated
tangentOneNECSaturationWitness = refl

tangentTwoNECSaturationWitness :
  directionalNEC Stress.tangentTwo ≡ conditionSaturated
tangentTwoNECSaturationWitness = refl

------------------------------------------------------------------------
-- Source-bounded reconstruction receipt.
------------------------------------------------------------------------

record BrownMaclayNormalizedStressWitness : Set₁ where
  constructor brown-maclay-normalized-stress-witness
  field
    sourceAuthority : BrownMaclay.BrownMaclayParallelPlateAuthority
    spatialStress : Stress.SpatialStressSheet ℚ
    energyDensity : ℚ

    energyDensityPattern : energyDensity ≡ - 1ℚ
    tangentOnePattern :
      spatialStress
        (Stress.plateTangentOneAxis , Stress.plateTangentOneAxis)
      ≡ 1ℚ
    tangentTwoPattern :
      spatialStress
        (Stress.plateTangentTwoAxis , Stress.plateTangentTwoAxis)
      ≡ 1ℚ
    normalPattern :
      Stress.normalPressure spatialStress ≡ - (Int.+ 3 / 1)

    finiteStressSourceBacked :
      BrownMaclay.zeroTemperatureFiniteStress sourceAuthority
    perfectPlateSystemSourceBacked :
      BrownMaclay.perfectConductingParallelPlates sourceAuthority

    reading : String

open BrownMaclayNormalizedStressWitness public

canonicalBrownMaclayNormalizedStressWitness :
  BrownMaclayNormalizedStressWitness
canonicalBrownMaclayNormalizedStressWitness =
  brown-maclay-normalized-stress-witness
    BrownMaclay.brownMaclay1969
    brownMaclayNormalizedSpatialStress
    normalizedEnergyDensity
    refl
    refl
    refl
    refl
    tt
    tt
    "Brown-Maclay supplies source authority for the finite ideal-plate electromagnetic vacuum stress; DASHI realizes its normalized principal-stress fingerprint on the existing 3x3 spatial operator sheet and derives the local energy-condition combinations."

------------------------------------------------------------------------
-- Same-object bridge to the existing arbitrary Casimir scalar kernel.
------------------------------------------------------------------------

record BrownMaclayKernelPressureWeld
    (kernel : Kernel.CasimirScalarModel)
    (d : Q.Length) : Set₁ where
  field
    scaleMap : ℚ → Kernel.Scalar kernel

    SameIdealPlateSystem : Set
    sameIdealPlateSystem : SameIdealPlateSystem

    normalizedNormalPressureAgreesWithKernel :
      scaleMap (Stress.normalPressure brownMaclayNormalizedSpatialStress)
      ≡ Kernel.pressure kernel d

    normalizedEnergyDensityHasSamePositiveScale : Set
    normalizedEnergyDensityHasSamePositiveScaleEvidence :
      normalizedEnergyDensityHasSamePositiveScale

    reading : String

open BrownMaclayKernelPressureWeld public

------------------------------------------------------------------------
-- GR / averaged-condition / engineering firewalls.
------------------------------------------------------------------------

data BrownMaclayCitationAutomaticallyConstructsSameObjectStress : Set where
data PointwiseNECViolationAutomaticallyViolatesANEC : Set where
data LocalNegativeEnergyAutomaticallyCreatesMacroscopicExoticMatter : Set where
data CasimirStressAutomaticallyMeasuresGRBackreaction : Set where
data NECViolationAutomaticallyImpliesNullDefocusingWithoutEinsteinEquation : Set where

brownMaclayCitationDoesNotConstructSameObjectStress :
  BrownMaclayCitationAutomaticallyConstructsSameObjectStress → ⊥
brownMaclayCitationDoesNotConstructSameObjectStress ()

pointwiseNECDoesNotAutomaticallySettleANEC :
  PointwiseNECViolationAutomaticallyViolatesANEC → ⊥
pointwiseNECDoesNotAutomaticallySettleANEC ()

localNegativeEnergyDoesNotCreateMacroscopicExoticMatter :
  LocalNegativeEnergyAutomaticallyCreatesMacroscopicExoticMatter → ⊥
localNegativeEnergyDoesNotCreateMacroscopicExoticMatter ()

casimirStressDoesNotMeasureGRBackreaction :
  CasimirStressAutomaticallyMeasuresGRBackreaction → ⊥
casimirStressDoesNotMeasureGRBackreaction ()

necDoesNotBecomeNullDefocusingWithoutGravityWeld :
  NECViolationAutomaticallyImpliesNullDefocusingWithoutEinsteinEquation → ⊥
necDoesNotBecomeNullDefocusingWithoutGravityWeld ()

------------------------------------------------------------------------
-- Terminal machine-readable status.
------------------------------------------------------------------------

record CasimirBrownMaclayEnergyConditionBoundary : Set where
  constructor casimir-brown-maclay-energy-condition-boundary
  field
    normalizedSpatialStressOwned : Bool
    sameSO3OperatorSheetUsed : Bool
    normalPressureMinusThreeOwned : Bool
    tangentialPressurePlusOneOwned : Bool
    offDiagonalNormalTractionZeroOwned : Bool
    lorentzTracelessnessOwned : Bool
    arbitraryNullDirectionFormulaOwned : Bool
    tangentialNECSaturationOwned : Bool
    normalNECViolationOwned : Bool
    WECViolationOwned : Bool
    SECViolationOwned : Bool
    DECViolationOwned : Bool
    BrownMaclaySourceAuthorityReused : Bool

    arbitraryKernelPressureSameObjectAutomaticallyPaid : Bool
    ANECViolationAutomaticallyClaimed : Bool
    GRBackreactionMeasured : Bool
    macroscopicExoticMatterClaimed : Bool
    nullDefocusingClaimedWithoutEinsteinEquation : Bool

open CasimirBrownMaclayEnergyConditionBoundary public

canonicalCasimirBrownMaclayEnergyConditionBoundary :
  CasimirBrownMaclayEnergyConditionBoundary
canonicalCasimirBrownMaclayEnergyConditionBoundary =
  casimir-brown-maclay-energy-condition-boundary
    true true true true true true true true true true true true true
    false false false false false

casimirBrownMaclayEnergyConditionReading : String
casimirBrownMaclayEnergyConditionReading =
  "On the normalized positive Casimir scale C, the ideal parallel-plate vacuum has rho=-C, tangential pressures +C,+C and normal pressure -3C on the same 3x3 spatial operator sheet. The four-dimensional stress is traceless. For an arbitrary null direction with normal squared weight w, T(k,k)=-4 C w: exactly parallel directions saturate NEC, while any positive normal component violates it. WEC, SEC and DEC also fail locally. These QFT stress statements do not by themselves settle ANEC, construct macroscopic exotic matter, measure gravitational backreaction, or imply null defocusing without a same-object semiclassical Einstein-equation weld."
