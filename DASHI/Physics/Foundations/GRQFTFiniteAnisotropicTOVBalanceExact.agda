{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTFiniteAnisotropicTOVBalanceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as Signed
import DASHI.Physics.Foundations.GRQFTLocalizedRepulsiveSourceCriterionExact as Local
import DASHI.Physics.Foundations.GRQFTLocalizedAnisotropicRepulsiveShellExact as Shell

------------------------------------------------------------------------
-- NORMALIZED FINITE ANISOTROPIC TOV BALANCE
--
-- The continuum anisotropic hydrostatic equation has the schematic form
--
--   p_r' =
--     - gravityFactor * (rho + p_r)
--     + 2 (p_t - p_r) / r.
--
-- We do NOT claim a full TOV derivation or metric solution here.  We isolate a
-- normalized unit-radius/unit-gravity finite balance to test whether the first
-- proposed shell has even the correct force orientation.
------------------------------------------------------------------------

normalizedRadius : ℚ
normalizedRadius = 1ℚ

normalizedGravityFactor : ℚ
normalizedGravityFactor = 1ℚ

normalizedAnisotropicTOVRHS :
  Shell.SphericalStressZone → ℚ
normalizedAnisotropicTOVRHS zone =
  - (normalizedGravityFactor * (Shell.rho zone + Shell.radialPressure zone))
  + (Int.+ 2 / 1)
      * (Shell.tangentialPressure zone - Shell.radialPressure zone)
      * (Int.+ 1 / 1)

------------------------------------------------------------------------
-- FIRST SHELL FAILS THE STATIC-BALANCE SIGN TEST
------------------------------------------------------------------------

originalBoundaryTOVRHSIsNegativeThree :
  normalizedAnisotropicTOVRHS Shell.boundaryZone
    ≡ - (Int.+ 3 / 1)
originalBoundaryTOVRHSIsNegativeThree = solve []

desiredOutwardRadialPressureStep : ℚ
desiredOutwardRadialPressureStep = 1ℚ

originalBoundaryDoesNotMatchDesiredPressureStep :
  normalizedAnisotropicTOVRHS Shell.boundaryZone
    ≡ desiredOutwardRadialPressureStep →
  ⊥
originalBoundaryDoesNotMatchDesiredPressureStep ()

------------------------------------------------------------------------
-- BALANCED THIN TRANSITION LAYER
--
-- Core remains vacuum-like:
--     (rho,p_r,p_t) = (1,-1,-1)
--
-- Transition layer:
--     (rho,p_r,p_t) = (1,0,+1)
--
-- At the normalized surface:
--
--   -(rho+p_r) + 2(p_t-p_r) = -1 + 2 = +1,
--
-- exactly matching the finite outward radial-pressure step from -1 to 0.
------------------------------------------------------------------------

balancedTransitionZone : Shell.SphericalStressZone
balancedTransitionZone =
  Shell.spherical-stress-zone
    1ℚ
    0ℚ
    1ℚ

balancedTransitionTOVRHSIsPositiveOne :
  normalizedAnisotropicTOVRHS balancedTransitionZone ≡ 1ℚ
balancedTransitionTOVRHSIsPositiveOne = solve []

balancedTransitionMatchesPressureStep :
  normalizedAnisotropicTOVRHS balancedTransitionZone
    ≡ desiredOutwardRadialPressureStep
balancedTransitionMatchesPressureStep =
  balancedTransitionTOVRHSIsPositiveOne

balancedTransitionRadialPressureZero :
  Shell.radialPressure balancedTransitionZone ≡ 0ℚ
balancedTransitionRadialPressureZero = refl

balancedTransitionActiveStressIsPositiveThree :
  Shell.activeStressDensity balancedTransitionZone
    ≡ Int.+ 3 / 1
balancedTransitionActiveStressIsPositiveThree = solve []

------------------------------------------------------------------------
-- THIN-SHELL WEIGHT KEEPS TOTAL ACTIVE MASS NEGATIVE
--
-- Equal weighting no longer works: the transition layer carries positive
-- active stress.  But a geometrically thin layer need not have core-sized
-- volume.  Choose normalized shell weight 1/2:
--
--   M_active = (-2)*1 + (+3)*(1/2) = -1/2.
------------------------------------------------------------------------

coreWeight : ℚ
coreWeight = 1ℚ

transitionWeight : ℚ
transitionWeight = Int.+ 1 / 2

balancedTwoZoneActiveMass : ℚ
balancedTwoZoneActiveMass =
  coreWeight * Shell.activeStressDensity Shell.coreZone
  + transitionWeight * Shell.activeStressDensity balancedTransitionZone

balancedTwoZoneActiveMassIsNegativeHalf :
  balancedTwoZoneActiveMass ≡ - (Int.+ 1 / 2)
balancedTwoZoneActiveMassIsNegativeHalf = solve []

------------------------------------------------------------------------
-- EXTERIOR RESPONSE
------------------------------------------------------------------------

balancedTwoZoneExteriorResponse :
  Local.ExteriorRadialResponse
balancedTwoZoneExteriorResponse =
  Local.exteriorResponse Signed.positiveCoupling Local.negativeActiveMass

balancedTwoZoneExteriorResponseIsOutward :
  balancedTwoZoneExteriorResponse ≡ Local.outwardExteriorAcceleration
balancedTwoZoneExteriorResponseIsOutward = refl

------------------------------------------------------------------------
-- COMPOSED BALANCED SHELL WITNESS
------------------------------------------------------------------------

record FiniteAnisotropicTOVBalanceWitness : Set where
  constructor finite-anisotropic-tov-balance-witness
  field
    core : Shell.SphericalStressZone
    transition : Shell.SphericalStressZone

    desiredPressureStep : ℚ

    transitionBalance :
      normalizedAnisotropicTOVRHS transition ≡ desiredPressureStep

    surfaceRadialPressureZero :
      Shell.radialPressure transition ≡ 0ℚ

    transitionWeightValue :
      transitionWeight ≡ Int.+ 1 / 2

    integratedActiveMass :
      balancedTwoZoneActiveMass ≡ - (Int.+ 1 / 2)

    coupling : Signed.CouplingSign
    couplingPositive :
      coupling ≡ Signed.positiveCoupling

    exteriorResponse :
      Local.ExteriorRadialResponse
    exteriorResponseOutward :
      exteriorResponse ≡ Local.outwardExteriorAcceleration

open FiniteAnisotropicTOVBalanceWitness public

canonicalFiniteAnisotropicTOVBalanceWitness :
  FiniteAnisotropicTOVBalanceWitness
canonicalFiniteAnisotropicTOVBalanceWitness =
  finite-anisotropic-tov-balance-witness
    Shell.coreZone
    balancedTransitionZone
    desiredOutwardRadialPressureStep
    balancedTransitionMatchesPressureStep
    balancedTransitionRadialPressureZero
    refl
    balancedTwoZoneActiveMassIsNegativeHalf
    Signed.positiveCoupling
    refl
    Local.outwardExteriorAcceleration
    refl

------------------------------------------------------------------------
-- BOUNDARY
------------------------------------------------------------------------

record FiniteAnisotropicTOVBalanceBoundary : Set where
  constructor finite-anisotropic-tov-balance-boundary
  field
    originalNegativeTangentialShellFailsBalanceSign : Bool
    positiveTangentialTransitionRepairsNormalizedBalance : Bool
    pressureFreeSurfaceRetained : Bool
    transitionMustBeThinEnoughForNetNegativeActiveMass : Bool
    explicitHalfWeightFixtureRemainsNegative : Bool
    positiveGExteriorRepulsionRetained : Bool
    fullTOVMetricFactorDerived : Bool
    conservationEquationContinuumSolved : Bool
    junctionConditionsSolved : Bool

canonicalFiniteAnisotropicTOVBalanceBoundary :
  FiniteAnisotropicTOVBalanceBoundary
canonicalFiniteAnisotropicTOVBalanceBoundary =
  finite-anisotropic-tov-balance-boundary
    true true true true true true false false false
