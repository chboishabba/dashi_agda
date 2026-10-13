{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkHistoryHorizonScalingExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

------------------------------------------------------------------------
-- MINIMAL QUANTITATIVE HISTORY/HORIZON SCALING MODEL
--
-- This is deliberately a model, not a microscopic derivation.  If a residual
-- history-sector density scales with H^2,
--
--   rho_H = alpha H^2,
--
-- while the critical-density carrier is represented as
--
--   rho_c = beta H^2,
--
-- then the cross-multiplied fractional-density relation is independent of H:
--
--   beta rho_H = alpha rho_c.
--
-- This is the exact algebraic content behind a coincidence/tracking proposal.
-- It does NOT derive alpha, beta, H^2 scaling, or observational Omega_DE.
------------------------------------------------------------------------

historyDensity : ℚ → ℚ → ℚ
historyDensity alpha hubble = alpha * hubble * hubble

criticalDensityCarrier : ℚ → ℚ → ℚ
criticalDensityCarrier beta hubble = beta * hubble * hubble

horizonTrackingCrossProduct :
  (alpha beta hubble : ℚ) →
  beta * historyDensity alpha hubble
    ≡ alpha * criticalDensityCarrier beta hubble
horizonTrackingCrossProduct alpha beta hubble = solve (alpha ∷ beta ∷ hubble ∷ [])

record HorizonTrackingModel : Set where
  constructor horizon-tracking-model
  field
    alpha : ℚ
    beta : ℚ
    historyDensityCoefficientSelected : Bool
    criticalDensityCoefficientSelected : Bool
    microscopicHubbleSquaredScalingDerived : Bool

open HorizonTrackingModel public

canonicalHorizonTrackingModel : HorizonTrackingModel
canonicalHorizonTrackingModel =
  horizon-tracking-model
    (Int.+ 7 / 10)
    1ℚ
    true true false

------------------------------------------------------------------------
-- Simple equation-of-state parameterisation.
--
-- For a phenomenological density law rho(a) ∝ a^{-n}, continuity gives
-- w = -1 + n/3.  Here we encode only that algebraic parameter map; deriving the
-- continuity equation and n from the history sector remains separate.
------------------------------------------------------------------------

wFromScalingExponent : ℚ → ℚ
wFromScalingExponent n = - 1ℚ + n / (Int.+ 3 / 1)

constantDensityGivesVacuumW :
  wFromScalingExponent 0ℚ ≡ - 1ℚ
constantDensityGivesVacuumW = solve []

unitExponentGivesMinusTwoThirds :
  wFromScalingExponent 1ℚ ≡ - (Int.+ 2 / 3)
unitExponentGivesMinusTwoThirds = solve []

activeStressFactor : ℚ → ℚ
activeStressFactor w = 1ℚ + (Int.+ 3 / 1) * w

vacuumWActiveStressFactor :
  activeStressFactor (- 1ℚ) ≡ - (Int.+ 2 / 1)
vacuumWActiveStressFactor = solve []

minusTwoThirdsActiveStressFactor :
  activeStressFactor (- (Int.+ 2 / 3)) ≡ - 1ℚ
minusTwoThirdsActiveStressFactor = solve []

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

hubbleSquaredTrackingAlgebraOwned : Bool
hubbleSquaredTrackingAlgebraOwned = true

constantFractionRequiresNoPlanckScaleInputAlgebraically : Bool
constantFractionRequiresNoPlanckScaleInputAlgebraically = true

microscopicHistorySectorHubbleSquaredScalingDerived : Bool
microscopicHistorySectorHubbleSquaredScalingDerived = false

observedDarkEnergyFractionDerived : Bool
observedDarkEnergyFractionDerived = false

continuityEquationDerivedHere : Bool
continuityEquationDerivedHere = false

historyScalingExponentDerived : Bool
historyScalingExponentDerived = false

coincidenceMechanismModelledNotSolved : Bool
coincidenceMechanismModelledNotSolved = true
