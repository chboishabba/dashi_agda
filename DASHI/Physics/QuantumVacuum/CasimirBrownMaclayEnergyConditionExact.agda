module DASHI.Physics.QuantumVacuum.CasimirBrownMaclayEnergyConditionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; _+_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Foundations.RecursiveRadixHypervoxel as HyperBase
import DASHI.Physics.Closure.SU2SO3369HypervoxelBridge as SO3
import DASHI.Physics.QuantumVacuum.BrownMaclayParallelPlateSourceAuthorityExact as BrownMaclay
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Kernel
import DASHI.Physics.QuantumVacuum.PhysicalQuantities as Q
import DASHI.Physics.QuantumVacuum.CasimirSO3StressContractionMaxCutExact as Stress

------------------------------------------------------------------------
-- BROWN-MACLAY PARALLEL-PLATE STRESS -> LOCAL ENERGY CONDITIONS
--
-- Work in units of the positive Casimir scale
--
--   C = pi^2 hbar c / (720 d^4) > 0.
--
-- The renormalized ideal-plate stress fingerprint is represented by
--
--   rho = -C
--   p_t1 = +C
--   p_t2 = +C
--   p_n  = -3C.
--
-- The spatial part therefore lives literally on the SO(3)-style 3x3 operator
-- sheet introduced by CasimirSO3StressContractionMaxCutExact.  Normalization
-- by C is deliberate: this file proves the exact coefficient/sign geometry;
-- a same-object map into an arbitrary CasimirScalarModel remains an explicit
-- weld below rather than being manufactured by rational arithmetic.
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

tangentNullCombinationIsZero :
  tangentNullCombination ≡ 0ℚ
tangentNullCombinationIsZero = solve []

normalNullCombinationIsNegativeFour :
  normalNullCombination ≡ - (Int.+ 4 / 1)
normalNullCombinationIsNegativeFour = solve []

activeStressCombinationIsNegativeTwo :
  activeStressCombination ≡ - (Int.+ 2 / 1)
activeStressCombinationIsNegativeTwo = solve []

------------------------------------------------------------------------
-- Direction-sensitive condition verdicts.
--
-- Tangential null directions saturate NEC.  A null direction normal to the
-- plates has rho+p_n = -4C < 0, so the pointwise NEC fails.  The static
-- observer already sees rho=-C<0, so WEC fails.  The active SEC combination
-- is -2C, and DEC fails already because rho is negative (also |p_n|>|rho|).
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
--
-- Brown-Maclay remains the source authority for the finite ideal conducting-
-- plate vacuum stress.  DASHI owns this normalized coefficient realization
-- and its operator-sheet / energy-condition composition.
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
--
-- The normalized rational fingerprint is not silently identified with an
-- arbitrary Scalar.  A concrete instance must provide the scale map and prove
-- that the normal-normal component is exactly the kernel pressure at the same
-- separation on the same ideal-plate system.
------------------------------------------------------------------------

record BrownMaclayKernelPressureWeld
    (kernel : Kernel.CasimirScalarModel)
    (d : Q.Length) : Set₁ where
  field
    scaleMap : ℚ → Kernel.CasimirScalarModel.Scalar kernel

    SameIdealPlateSystem : Set
    sameIdealPlateSystem : SameIdealPlateSystem

    normalizedNormalPressureAgreesWithKernel :
      scaleMap (Stress.normalPressure brownMaclayNormalizedSpatialStress)
      ≡ Kernel.CasimirScalarModel.pressure kernel d

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
    true true true true true true true true true true true
    false false false false false

casimirBrownMaclayEnergyConditionReading : String
casimirBrownMaclayEnergyConditionReading =
  "On the normalized positive Casimir scale C, the ideal parallel-plate vacuum has rho=-C, tangential pressures +C,+C and normal pressure -3C on the same 3x3 spatial operator sheet. Tangential null directions saturate NEC while the normal null direction gives rho+p_n=-4C and violates NEC. WEC, SEC and DEC also fail locally. These QFT stress statements do not by themselves settle ANEC, construct macroscopic exotic matter, measure gravitational backreaction, or imply null defocusing without a same-object semiclassical Einstein-equation weld."
