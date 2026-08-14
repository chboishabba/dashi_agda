module DASHI.Cognition.PNF.FutureRateDistortionGenericExact where

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)
import Data.Rational.Properties as ℚₚ

record RateDistortionFamily : Set₁ where
  constructor rateDistortionFamily
  field
    Candidate : Set
    rate : Candidate → Nat
    distortion : Candidate → ℚ

open RateDistortionFamily public

Feasible : (family : RateDistortionFamily) → ℚ → Candidate family → Set
Feasible family epsilon candidate = distortion family candidate ≤ epsilon

record OptimalAt
    (family : RateDistortionFamily)
    (epsilon : ℚ) : Set₁ where
  constructor optimalAt
  field
    selected : Candidate family
    selectedFeasible : Feasible family epsilon selected
    selectedMinimal :
      (candidate : Candidate family) →
      Feasible family epsilon candidate →
      rate family selected ≤ rate family candidate

open OptimalAt public

feasibilityMonotone :
  ∀ {family epsilon epsilon′ candidate} →
  epsilon ≤ epsilon′ →
  Feasible family epsilon candidate →
  Feasible family epsilon′ candidate
feasibilityMonotone epsilon≤epsilon′ feasible =
  ℚₚ.≤-trans feasible epsilon≤epsilon′

optimalRateAntitoneInTolerance :
  ∀ {family epsilon epsilon′} →
  epsilon ≤ epsilon′ →
  (tight : OptimalAt family epsilon) →
  (loose : OptimalAt family epsilon′) →
  rate family (selected loose) ≤ rate family (selected tight)
optimalRateAntitoneInTolerance epsilon≤epsilon′ tight loose =
  selectedMinimal loose
    (selected tight)
    (feasibilityMonotone epsilon≤epsilon′ (selectedFeasible tight))

record ZeroDistortionSafety
    (family : RateDistortionFamily)
    (Safe : Candidate family → Set) : Set₁ where
  constructor zeroDistortionSafety
  field
    zeroFeasibleIsSafe :
      (candidate : Candidate family) →
      Feasible family 0ℚ candidate →
      Safe candidate

open ZeroDistortionSafety public

zeroDistortionOptimumIsSafe :
  ∀ {family Safe} →
  ZeroDistortionSafety family Safe →
  (optimum : OptimalAt family 0ℚ) →
  Safe (selected optimum)
zeroDistortionOptimumIsSafe safety optimum =
  zeroFeasibleIsSafe safety (selected optimum) (selectedFeasible optimum)

------------------------------------------------------------------------
-- This is the abstract R_C(epsilon) theorem surface.  It deliberately does not
-- assert Shannon asymptotic coding or existence of an optimum for arbitrary
-- infinite candidate families; concrete finite families supply OptimalAt.
------------------------------------------------------------------------
