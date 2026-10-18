{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityTOVSourceToRadialObservableBidiExact where

------------------------------------------------------------------------
-- EXACT SOURCE -> EINSTEIN/TOV -> RADIAL RESPONSE, BIDIRECTIONAL
--
-- In G=c=1 with the same 4*pi-absorbed radial pressure convention as the
-- repo's finite rational TOV owner, a static spherically symmetric metric
--
-- ds² = -exp(2Phi(r))dt² + (1-2m(r)/r)^-1 dr² + r²dOmega²
--
-- obeys Phi' = (m + r³ p_r) / [r(r-2m)].
-- For a radially initially-resting geodesic, the proper-time second
-- derivative of the areal radius follows as - (m+r³p_r)/r² at that instant. (It is not the static observer's
-- proper acceleration, nor d²r/dt² with Killing coordinate time;
-- a physical clock/probe calibration is separate.)
--
-- The *numerator* m+r³p_r, NOT rho+p_r+2p_t, determines this local
-- initially-resting geodesic orientation for the TOV metric. This is a
-- useful second observable to compare with active-stress defocusing.
--
-- Physical metric/stress identification with the literal CMP119 finite
-- measure remains a necessary source theorem; these are exact TOV results.
--
-- Source: TOV equations; see GRQFTFiniteRationalTOVSystemExact.
-- New DASHI derivation: two contrasting nodes of the SAME existing TOV
-- sample exhibit outward local acceleration versus inward vacuum-boundary
-- response even when the finite integrated active stress is negative.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _/_)
import Data.Integer.Base as Int
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.Foundations.GRQFTFiniteRationalTOVSystemExact as TOV
import DASHI.Physics.Foundations.GRQFTSchwarzschildDeSitterExteriorEscapeExact as Exterior

-- This directly evaluates a physical observable from the pre-existing
-- TOV state. No free Antigravity or NegativeActiveStress conclusion field.
radialInitiallyRestingAcceleration : TOV.RationalRadialState → ℚ
radialInitiallyRestingAcceleration s =
  - (TOV.tovGravityNumerator s /
      (TOV.radius s * TOV.radius s))

radialPressureMassNumerator :
  TOV.RationalRadialState → ℚ
radialPressureMassNumerator = TOV.tovGravityNumerator

innerMassPressureNumeratorIsMinusSevenEighths :
  radialPressureMassNumerator TOV.innerState
    ≡ - (Int.+ 7 / 8)
innerMassPressureNumeratorIsMinusSevenEighths = solve []

innerInitiallyRestingAccelerationIsSevenEighths :
  radialInitiallyRestingAcceleration TOV.innerState
    ≡ Int.+ 7 / 8
innerInitiallyRestingAccelerationIsSevenEighths = solve []

outerMassPressureNumeratorIsPositiveQuarter :
  radialPressureMassNumerator TOV.outerBalancedState
    ≡ Int.+ 1 / 4
outerMassPressureNumeratorIsPositiveQuarter = solve []

outerInitiallyRestingAccelerationIsMinusOneSixteenth :
  radialInitiallyRestingAcceleration TOV.outerBalancedState
    ≡ - (Int.+ 1 / 16)
outerInitiallyRestingAccelerationIsMinusOneSixteenth = solve []

-- At a zero-pressure surface, the proper-time areal-radius acceleration in the same
-- normalized Schwarzschild gauge is the standard vacuum Schwarzschild
-- acceleration: -(M/R²). This is a mathematical identity on the model.
outerInitiallyRestingIsSchwarzschild :
  radialInitiallyRestingAcceleration TOV.outerBalancedState
  ≡ Exterior.kottlerRadialAcceleration
      TOV.outerMassTarget TOV.outerRadius 0ℚ
outerInitiallyRestingIsSchwarzschild = solve []

-- Critical distinction: negative integrated active mass in the TOV
-- example does not imply outward exterior Schwarzschild acceleration.
finiteIntegratedActiveMassStillNegative :
  TOV.finiteIntegratedActiveMass ≡ - (Int.+ 11 / 12)
finiteIntegratedActiveMassStillNegative =
  TOV.finiteIntegratedActiveMassIsNegativeElevenTwelfths

-- The negative integrated-active-stress fixture and its outward interior
-- test-body response are NOT yet a complete global Einstein solution:
-- continuity, surface stresses and full covariant conservation still matter.
