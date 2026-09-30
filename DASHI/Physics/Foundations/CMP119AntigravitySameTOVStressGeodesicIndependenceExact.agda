{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySameTOVStressGeodesicIndependenceExact where

------------------------------------------------------------------------
-- SOURCE-NATIVE TWO OBSERVABLES, BIDIRECTIONAL COMPARISON
--
-- The physical gravitating source has rho, p_r, p_t as components of ONE
-- radial stress state, never a separately selected trace sign.
--
-- Local timelike convergence source: A = rho + p_r + 2p_t.
-- Local initially-resting radial geodesic response in static spherical
-- Einstein/TOV geometry: -[m+r³p_r]/r² (proper-time radial second derivative).
--
-- These observables are independent at a point, even in the static patch:
-- pressure anisotropy can change A without changing the radial acceleration.
-- This forbids an invalid transport negative(A) => outward acceleration.
--
-- The explicit fixtures below are radial constraint DATA, not globally
-- integrated solutions with proved TOV conservation/junction conditions.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _/_)
import Data.Integer.Base as Int
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Foundations.GRQFTFiniteRationalTOVSystemExact as TOV
import DASHI.Physics.Foundations.CMP119AntigravityTraceVsActiveStressFirewallExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityTOVSourceToRadialObservableBidiExact as Radial

oneSourceLorentzianTrace : TOV.RationalRadialState → ℚ
oneSourceLorentzianTrace s =
  Trace.lorentzianTrace
    (TOV.rho s)
    (TOV.radialPressure s)
    (TOV.tangentialPressure s)
    (TOV.tangentialPressure s)

oneSourceLorentzianActive : TOV.RationalRadialState → ℚ
oneSourceLorentzianActive s =
  Trace.lorentzianActiveStress
    (TOV.rho s)
    (TOV.radialPressure s)
    (TOV.tangentialPressure s)
    (TOV.tangentialPressure s)

sameTensorTraceIsActiveMinusTwoRho :
  ∀ s →
  oneSourceLorentzianActive s
  ≡ oneSourceLorentzianTrace s
     + (1ℚ + 1ℚ) * TOV.rho s
sameTensorTraceIsActiveMinusTwoRho s =
  Trace.activeStressIsTracePlusTwiceEnergyDensity
    (TOV.rho s) (TOV.radialPressure s)
    (TOV.tangentialPressure s) (TOV.tangentialPressure s)

sameTensorActiveIsExistingTOVActive :
  ∀ s →
  oneSourceLorentzianActive s ≡ TOV.activeStress s
sameTensorActiveIsExistingTOVActive s =
  solve (TOV.rho s Int.∷ TOV.radialPressure s Int.∷
    TOV.tangentialPressure s Int.∷ [])

-- Two static-patch local fixtures have identical m/r and positive rho.
-- Only the radial/tangential pressure allocations differ.
localNegativeActiveButInward : TOV.RationalRadialState
localNegativeActiveButInward =
  TOV.rational-radial-state
    1ℚ (Int.+ 1 / 8) 1ℚ 1ℚ 0ℚ (- 1ℚ)

localPositiveActiveButOutward : TOV.RationalRadialState
localPositiveActiveButOutward =
  TOV.rational-radial-state
    1ℚ (Int.+ 1 / 8) 1ℚ 1ℚ (- 1ℚ) 1ℚ

negativeActiveFixtureHasNegativeActive :
  oneSourceLorentzianActive localNegativeActiveButInward ≡ - 1ℚ
negativeActiveFixtureHasNegativeActive = solve []

negativeActiveFixtureAcceleratesInward :
  Radial.radialInitiallyRestingAcceleration
    localNegativeActiveButInward ≡ - (Int.+ 1 / 8)
negativeActiveFixtureAcceleratesInward = solve []

positiveActiveFixtureHasPositiveActive :
  oneSourceLorentzianActive localPositiveActiveButOutward
  ≡ Int.+ 2 / 1
positiveActiveFixtureHasPositiveActive = solve []

positiveActiveFixtureAcceleratesOutward :
  Radial.radialInitiallyRestingAcceleration
    localPositiveActiveButOutward ≡ Int.+ 7 / 8
positiveActiveFixtureAcceleratesOutward = solve []

negativeActiveFixtureIsStaticPatch :
  TOV.radius localNegativeActiveButInward
  - (Int.+ 2 / 1) * TOV.mass localNegativeActiveButInward
  ≡ Int.+ 3 / 4
negativeActiveFixtureIsStaticPatch = solve []

positiveActiveFixtureIsStaticPatch :
  TOV.radius localPositiveActiveButOutward
  - (Int.+ 2 / 1) * TOV.mass localPositiveActiveButOutward
  ≡ Int.+ 3 / 4
positiveActiveFixtureIsStaticPatch = solve []

-- A global outward response requires the m+r³p_r sign at the probe
-- (and junction/metric realization), NOT only the local stress trace sign.
