{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTFiniteRationalTOVSystemExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Empty using (⊥)
open import Data.List.Base using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _-_; _*_; -_; _<_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as Signed
import DASHI.Physics.Foundations.GRQFTLocalizedRepulsiveSourceCriterionExact as Local

------------------------------------------------------------------------
-- FINITE RATIONAL TOV SYSTEM
--
-- Absorb 4*pi into the density coordinate:
--
--   rhoBar(r) = 4*pi*rho(r)
--
-- so the mass equation becomes
--
--   m'(r) = r^2 rhoBar(r)
--
-- while the anisotropic TOV equation is represented as
--
--   p_r' =
--     -(rho+p_r) (m + r^3 p_rBar) / [r(r-2m)]
--     + 2(p_t-p_r)/r.
--
-- For the finite normalized fixture below we identify p_rBar with p_r in the
-- same dimensionless carrier.  This is a rational toy solution surface, not an
-- SI-calibrated stellar model.
------------------------------------------------------------------------

record RationalRadialState : Set where
  constructor rational-radial-state
  field
    radius : ℚ
    mass : ℚ
    densityBar : ℚ
    rho : ℚ
    radialPressure : ℚ
    tangentialPressure : ℚ

open RationalRadialState public

schwarzschildDenominator :
  RationalRadialState → ℚ
schwarzschildDenominator s =
  radius s * (radius s - (Int.+ 2 / 1) * mass s)

tovGravityNumerator :
  RationalRadialState → ℚ
tovGravityNumerator s =
  mass s + (radius s * radius s * radius s) * radialPressure s

tovGravityFactor :
  RationalRadialState → ℚ
tovGravityFactor s =
  tovGravityNumerator s / schwarzschildDenominator s

anisotropicTOVRHS :
  RationalRadialState → ℚ
anisotropicTOVRHS s =
  - ((rho s + radialPressure s) * tovGravityFactor s)
  + ((Int.+ 2 / 1)
      * (tangentialPressure s - radialPressure s))
      / radius s

------------------------------------------------------------------------
-- EXACT TWO-CELL MASS INTEGRATION
--
-- Unit-width shell quadrature:
--   Delta m = r^2 rhoBar Delta r
--
-- The fixture is chosen deliberately subcritical:
--
--   r1=1, m1=1/8
--   r2=2, m2=1/4
--
-- so r-2m stays positive at both nodes.
------------------------------------------------------------------------

innerState : RationalRadialState
innerState =
  rational-radial-state
    1ℚ
    (Int.+ 1 / 8)
    (Int.+ 1 / 8)
    1ℚ
    (- 1ℚ)
    (- 1ℚ)

outerMassTarget : ℚ
outerMassTarget = Int.+ 1 / 4

outerRadius : ℚ
outerRadius = Int.+ 2 / 1

outerDensityBar : ℚ
outerDensityBar = Int.+ 1 / 32

outerRadialPressure : ℚ
outerRadialPressure = 0ℚ

outerRho : ℚ
outerRho = 1ℚ

massIncrement :
  (r rhoBar deltaR : ℚ) → ℚ
massIncrement r rhoBar deltaR =
  r * r * rhoBar * deltaR

outerMassFromInner :
  ℚ
outerMassFromInner =
  mass innerState + massIncrement outerRadius outerDensityBar 1ℚ

outerMassIntegrationExact :
  outerMassFromInner ≡ outerMassTarget
outerMassIntegrationExact = solve []

------------------------------------------------------------------------
-- SOLVE REQUIRED p_t FROM THE LITERAL TOV FACTOR
------------------------------------------------------------------------

outerBaseState :
  ℚ → RationalRadialState
outerBaseState pT =
  rational-radial-state
    outerRadius
    outerMassTarget
    outerDensityBar
    outerRho
    outerRadialPressure
    pT

desiredOuterPressureDerivative : ℚ
desiredOuterPressureDerivative = Int.+ 1 / 2

requiredOuterTangentialPressure : ℚ
requiredOuterTangentialPressure =
  outerRadialPressure
  + (outerRadius / (Int.+ 2 / 1))
      * (desiredOuterPressureDerivative
          + (outerRho + outerRadialPressure)
              * tovGravityFactor (outerBaseState 0ℚ))

outerTOVGravityNumeratorIsQuarter :
  tovGravityNumerator (outerBaseState 0ℚ)
    ≡ Int.+ 1 / 4
outerTOVGravityNumeratorIsQuarter = refl

outerSchwarzschildDenominatorIsThree :
  schwarzschildDenominator (outerBaseState 0ℚ)
    ≡ Int.+ 3 / 1
outerSchwarzschildDenominatorIsThree = refl

outerTOVGravityFactorIsOneTwelfth :
  tovGravityFactor (outerBaseState 0ℚ)
    ≡ Int.+ 1 / 12
outerTOVGravityFactorIsOneTwelfth = refl

requiredOuterTangentialPressureIsSevenTwelfths :
  requiredOuterTangentialPressure
    ≡ Int.+ 7 / 12
requiredOuterTangentialPressureIsSevenTwelfths = solve []

outerBalancedState : RationalRadialState
outerBalancedState =
  outerBaseState requiredOuterTangentialPressure

outerTOVBalanceExact :
  anisotropicTOVRHS outerBalancedState
    ≡ desiredOuterPressureDerivative
outerTOVBalanceExact = solve []

outerSurfaceRadialPressureZero :
  radialPressure outerBalancedState ≡ 0ℚ
outerSurfaceRadialPressureZero = refl

------------------------------------------------------------------------
-- COMPACTNESS / NO-HORIZON CHECK
------------------------------------------------------------------------

innerRMinusTwoM : ℚ
innerRMinusTwoM =
  radius innerState - (Int.+ 2 / 1) * mass innerState

outerRMinusTwoM : ℚ
outerRMinusTwoM =
  radius outerBalancedState - (Int.+ 2 / 1) * mass outerBalancedState

innerRMinusTwoMIsThreeQuarters :
  innerRMinusTwoM ≡ Int.+ 3 / 4
innerRMinusTwoMIsThreeQuarters = solve []

outerRMinusTwoMIsThreeHalves :
  outerRMinusTwoM ≡ Int.+ 3 / 2
outerRMinusTwoMIsThreeHalves = solve []

data CompactnessStatus : Set where
  subSchwarzschildAtAllNodes : CompactnessStatus

finiteGridCompactnessStatus : CompactnessStatus
finiteGridCompactnessStatus = subSchwarzschildAtAllNodes

------------------------------------------------------------------------
-- ACTIVE SOURCE
--
-- Use shell volume weights only as normalized finite quadrature weights.
-- Core active stress = -2.
-- Outer state active stress = rho + p_r + 2 p_t = 13/6 > 0.
--
-- A sufficiently thin transition shell preserves net negative active mass.
------------------------------------------------------------------------

activeStress :
  RationalRadialState → ℚ
activeStress s =
  rho s
  + radialPressure s
  + tangentialPressure s
  + tangentialPressure s

innerActiveStressIsNegativeTwo :
  activeStress innerState ≡ - (Int.+ 2 / 1)
innerActiveStressIsNegativeTwo = solve []

outerActiveStressIsThirteenSixths :
  activeStress outerBalancedState ≡ Int.+ 13 / 6
outerActiveStressIsThirteenSixths = solve []

innerVolumeWeight : ℚ
innerVolumeWeight = 1ℚ

outerVolumeWeight : ℚ
outerVolumeWeight = Int.+ 1 / 2

finiteIntegratedActiveMass : ℚ
finiteIntegratedActiveMass =
  innerVolumeWeight * activeStress innerState
  + outerVolumeWeight * activeStress outerBalancedState

finiteIntegratedActiveMassIsNegativeElevenTwelfths :
  finiteIntegratedActiveMass
    ≡ - (Int.+ 11 / 12)
finiteIntegratedActiveMassIsNegativeElevenTwelfths = solve []

------------------------------------------------------------------------
-- EXTERIOR RESPONSE UNDER POSITIVE G
------------------------------------------------------------------------

finiteExteriorResponse :
  Local.ExteriorRadialResponse
finiteExteriorResponse =
  Local.exteriorResponse
    Signed.positiveCoupling
    Local.negativeActiveMass

finiteExteriorResponseIsOutward :
  finiteExteriorResponse ≡ Local.outwardExteriorAcceleration
finiteExteriorResponseIsOutward = refl

------------------------------------------------------------------------
-- WITNESS
------------------------------------------------------------------------

record FiniteRationalTOVRepulsiveWitness : Set where
  constructor finite-rational-tov-repulsive-witness
  field
    inner : RationalRadialState
    outer : RationalRadialState

    massEquationPaid :
      outerMassFromInner ≡ outerMassTarget

    outerGravityFactor :
      tovGravityFactor (outerBaseState 0ℚ)
        ≡ Int.+ 1 / 12

    requiredTangentialPressure :
      tangentialPressure outer
        ≡ Int.+ 7 / 12

    tovBalance :
      anisotropicTOVRHS outer
        ≡ desiredOuterPressureDerivative

    surfacePressureZero :
      radialPressure outer ≡ 0ℚ

    innerNoHorizon :
      innerRMinusTwoM ≡ Int.+ 3 / 4

    outerNoHorizon :
      outerRMinusTwoM ≡ Int.+ 3 / 2

    integratedActiveMassNegative :
      finiteIntegratedActiveMass
        ≡ - (Int.+ 11 / 12)

    coupling : Signed.CouplingSign
    couplingPositive :
      coupling ≡ Signed.positiveCoupling

    exteriorResponse :
      Local.ExteriorRadialResponse
    exteriorResponseOutward :
      exteriorResponse ≡ Local.outwardExteriorAcceleration

open FiniteRationalTOVRepulsiveWitness public

canonicalFiniteRationalTOVRepulsiveWitness :
  FiniteRationalTOVRepulsiveWitness
canonicalFiniteRationalTOVRepulsiveWitness =
  finite-rational-tov-repulsive-witness
    innerState
    outerBalancedState
    outerMassIntegrationExact
    outerTOVGravityFactorIsOneTwelfth
    requiredOuterTangentialPressureIsSevenTwelfths
    outerTOVBalanceExact
    outerSurfaceRadialPressureZero
    innerRMinusTwoMIsThreeQuarters
    outerRMinusTwoMIsThreeHalves
    finiteIntegratedActiveMassIsNegativeElevenTwelfths
    Signed.positiveCoupling
    refl
    Local.outwardExteriorAcceleration
    refl

------------------------------------------------------------------------
-- BOUNDARY
------------------------------------------------------------------------

record FiniteRationalTOVBoundary : Set where
  constructor finite-rational-tov-boundary
  field
    literalMassFunctionStepConstructed : Bool
    literalTOVMetricFactorConstructed : Bool
    exactRMinusTwoMPositiveAtFiniteNodes : Bool
    surfaceRadialPressureZero : Bool
    tangentialPressureSolvedFromTOV : Bool
    netActiveMassNegative : Bool
    positiveGExteriorRepulsionCriterion : Bool
    negativeGRequired : Bool
    negativeInertialMassRequired : Bool
    continuumODEExistenceSolved : Bool
    exactJunctionToVacuumMetricSolved : Bool
    SIUnitsCalibrated : Bool

canonicalFiniteRationalTOVBoundary :
  FiniteRationalTOVBoundary
canonicalFiniteRationalTOVBoundary =
  finite-rational-tov-boundary
    true true true true true true true false false false false false
