{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTLocalizedAnisotropicRepulsiveShellExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as Signed
import DASHI.Physics.Foundations.GRQFTLocalizedRepulsiveSourceCriterionExact as Local

------------------------------------------------------------------------
-- TWO-ZONE LOCALIZED ANISOTROPIC SHELL
--
-- Goal: move beyond a homogeneous FLRW/vacuum-energy pattern toward a compact
-- source that can meet a pressure-free exterior boundary.
--
-- A pure isotropic p=-rho phase with rho>0 has p_r=-rho at its edge, so it
-- cannot simultaneously retain rho>0 and satisfy p_r=0 at the same sharp
-- vacuum boundary.  The smallest finite repair is an anisotropic transition
-- shell:
--
--   core:     rho=1, p_r=-1, p_t=-1
--   boundary: rho=1, p_r= 0, p_t=-1
--
-- Both zones have positive energy density.  The boundary radial pressure is
-- zero, while tangential tension preserves a negative active source.
------------------------------------------------------------------------

record SphericalStressZone : Set where
  constructor spherical-stress-zone
  field
    rho : ℚ
    radialPressure : ℚ
    tangentialPressure : ℚ

open SphericalStressZone public

activeStressDensity :
  SphericalStressZone → ℚ
activeStressDensity zone =
  rho zone
  + radialPressure zone
  + tangentialPressure zone
  + tangentialPressure zone

coreZone : SphericalStressZone
coreZone =
  spherical-stress-zone
    1ℚ
    (- 1ℚ)
    (- 1ℚ)

boundaryZone : SphericalStressZone
boundaryZone =
  spherical-stress-zone
    1ℚ
    0ℚ
    (- 1ℚ)

coreActiveStressIsNegativeTwo :
  activeStressDensity coreZone ≡ - (Int.+ 2 / 1)
coreActiveStressIsNegativeTwo = solve []

boundaryActiveStressIsNegativeOne :
  activeStressDensity boundaryZone ≡ - 1ℚ
boundaryActiveStressIsNegativeOne = solve []

boundaryRadialPressureVanishes :
  radialPressure boundaryZone ≡ 0ℚ
boundaryRadialPressureVanishes = refl

boundaryEnergyDensityPositive :
  rho boundaryZone ≡ 1ℚ
boundaryEnergyDensityPositive = refl

boundaryTangentialTensionNegative :
  tangentialPressure boundaryZone ≡ - 1ℚ
boundaryTangentialTensionNegative = refl

------------------------------------------------------------------------
-- WHY ANISOTROPY IS NEEDED AT THE COMPACT EDGE
------------------------------------------------------------------------

isotropicVacuumLikeZone :
  ℚ → SphericalStressZone
isotropicVacuumLikeZone density =
  spherical-stress-zone density (- density) (- density)

isotropicPositiveUnitRadialPressure :
  radialPressure (isotropicVacuumLikeZone 1ℚ) ≡ - 1ℚ
isotropicPositiveUnitRadialPressure = refl

isotropicPositiveUnitCannotAlsoHaveZeroRadialBoundaryPressure :
  radialPressure (isotropicVacuumLikeZone 1ℚ) ≡ 0ℚ → ⊥
isotropicPositiveUnitCannotAlsoHaveZeroRadialBoundaryPressure ()

------------------------------------------------------------------------
-- SIMPLE ENERGY-CONDITION DIAGNOSTICS
--
-- These are exact algebraic values, not a promotion to a complete matter
-- model.  For the chosen shell:
--
--   rho + p_r = 1 >= 0
--   rho + p_t = 0
--   |p_r| <= rho and |p_t| = rho by inspection of the normalized values
--   rho + p_r + 2 p_t = -1 < 0
--
-- Thus the shell can retain the usual null/weak-condition sign pattern while
-- violating the strong active-gravity combination.
------------------------------------------------------------------------

boundaryRadialNullCombination :
  rho boundaryZone + radialPressure boundaryZone ≡ 1ℚ
boundaryRadialNullCombination = solve []

boundaryTangentialNullCombination :
  rho boundaryZone + tangentialPressure boundaryZone ≡ 0ℚ
boundaryTangentialNullCombination = solve []

data EnergyConditionPattern : Set where
  nullWeakCompatibleStrongViolated : EnergyConditionPattern

boundaryEnergyConditionPattern : EnergyConditionPattern
boundaryEnergyConditionPattern =
  nullWeakCompatibleStrongViolated

------------------------------------------------------------------------
-- TWO-ZONE INTEGRATED ACTIVE SOURCE
--
-- Equal positive unit weights are used only as the smallest exact finite
-- fixture.  The active source remains negative after adding the transition
-- shell.
------------------------------------------------------------------------

coreWeight : ℚ
coreWeight = 1ℚ

boundaryWeight : ℚ
boundaryWeight = 1ℚ

twoZoneIntegratedActiveMass : ℚ
twoZoneIntegratedActiveMass =
  coreWeight * activeStressDensity coreZone
  + boundaryWeight * activeStressDensity boundaryZone

twoZoneIntegratedActiveMassIsNegativeThree :
  twoZoneIntegratedActiveMass ≡ - (Int.+ 3 / 1)
twoZoneIntegratedActiveMassIsNegativeThree = solve []

data IntegratedActiveMassSign : Set where
  integratedPositive : IntegratedActiveMassSign
  integratedZero : IntegratedActiveMassSign
  integratedNegative : IntegratedActiveMassSign

twoZoneIntegratedActiveMassSign : IntegratedActiveMassSign
twoZoneIntegratedActiveMassSign = integratedNegative

------------------------------------------------------------------------
-- EXTERNAL RESPONSE UNDER POSITIVE G
------------------------------------------------------------------------

twoZoneExteriorResponse :
  Local.ExteriorRadialResponse
twoZoneExteriorResponse =
  Local.exteriorResponse
    Signed.positiveCoupling
    Local.negativeActiveMass

twoZonePositiveGExteriorResponseIsOutward :
  twoZoneExteriorResponse ≡ Local.outwardExteriorAcceleration
twoZonePositiveGExteriorResponseIsOutward = refl

------------------------------------------------------------------------
-- COMPOSED LOCALIZED SHELL WITNESS
------------------------------------------------------------------------

record LocalizedAnisotropicRepulsiveShellWitness : Set where
  constructor localized-anisotropic-repulsive-shell-witness
  field
    core : SphericalStressZone
    boundary : SphericalStressZone

    coreActiveNegative :
      activeStressDensity core ≡ - (Int.+ 2 / 1)

    boundaryActiveNegative :
      activeStressDensity boundary ≡ - 1ℚ

    outerRadialPressureZero :
      radialPressure boundary ≡ 0ℚ

    outerDensityPositive :
      rho boundary ≡ 1ℚ

    outerTangentialTensionNegative :
      tangentialPressure boundary ≡ - 1ℚ

    integratedActiveMassNegative :
      twoZoneIntegratedActiveMass ≡ - (Int.+ 3 / 1)

    coupling : Signed.CouplingSign
    couplingPositive :
      coupling ≡ Signed.positiveCoupling

    externalResponse :
      Local.ExteriorRadialResponse
    externalResponseOutward :
      externalResponse ≡ Local.outwardExteriorAcceleration

open LocalizedAnisotropicRepulsiveShellWitness public

canonicalLocalizedAnisotropicRepulsiveShellWitness :
  LocalizedAnisotropicRepulsiveShellWitness
canonicalLocalizedAnisotropicRepulsiveShellWitness =
  localized-anisotropic-repulsive-shell-witness
    coreZone
    boundaryZone
    coreActiveStressIsNegativeTwo
    boundaryActiveStressIsNegativeOne
    boundaryRadialPressureVanishes
    boundaryEnergyDensityPositive
    boundaryTangentialTensionNegative
    twoZoneIntegratedActiveMassIsNegativeThree
    Signed.positiveCoupling
    refl
    Local.outwardExteriorAcceleration
    refl

------------------------------------------------------------------------
-- BOUNDARY
------------------------------------------------------------------------

record LocalizedAnisotropicRepulsiveShellBoundary : Set where
  constructor localized-anisotropic-repulsive-shell-boundary
  field
    positiveDensityRetained : Bool
    pressureFreeOuterRadialBoundaryConstructed : Bool
    tangentialTensionRetainedAtBoundary : Bool
    integratedActiveSourceNegative : Bool
    positiveGExteriorRepulsionCriterion : Bool
    negativeGRequired : Bool
    negativeInertialMassRequired : Bool
    isotropicSharpBoundarySufficient : Bool
    anisotropicTransitionRepairsBoundaryPressure : Bool
    fullTOVConservationEquationSolved : Bool
    exactStaticMetricSolved : Bool

canonicalLocalizedAnisotropicRepulsiveShellBoundary :
  LocalizedAnisotropicRepulsiveShellBoundary
canonicalLocalizedAnisotropicRepulsiveShellBoundary =
  localized-anisotropic-repulsive-shell-boundary
    true true true true true false false false true false false
