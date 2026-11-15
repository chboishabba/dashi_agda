{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkHistoryHorizonScalingExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

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
