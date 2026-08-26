module DASHI.Core.LogisticFoldCriticalityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Robert M. May,
-- "Simple mathematical models with very complicated dynamics",
-- Nature 261 (1976), 459--467.
-- DOI: 10.1038/261459a0.
--
-- DASHI CONTRIBUTION
--
-- Extract only the elementary exact algebra of the quadratic logistic family
--
--   f_r(x) = r x (1-x).
--
-- The point x = 1/2 is the fold/critical point of this quadratic because the
-- formal derivative r(1-2x) vanishes there, and the map is symmetric under
-- x |-> 1-x.  This finite algebra is useful to distinguish the logistic role
-- of 1/2 from the unrelated branching and Riemann-critical-line roles already
-- present in DASHI.
--
-- No claim is made here about a specific chaotic parameter, Lyapunov exponent,
-- empirical decision threshold, or an identification with the RH critical
-- line.  Those require separate structure.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)
open import Data.Integer using (+_)
open import Data.Rational as R using (_/_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

half : ℚ
half = (+ 1) R./ 2

logistic : ℚ → ℚ → ℚ
logistic r x = r * x * (1ℚ - x)

logisticDerivative : ℚ → ℚ → ℚ
logisticDerivative r x = r * (1ℚ - ((+ 2) R./ 1) * x)

logisticDerivativeAtHalfIsZero :
  (r : ℚ) → logisticDerivative r half ≡ 0ℚ
logisticDerivativeAtHalfIsZero r =
  solve (r ∷ [])

logisticComplementSymmetry :
  (r x : ℚ) → logistic r (1ℚ - x) ≡ logistic r x
logisticComplementSymmetry r x =
  solve (r ∷ x ∷ [])

logisticAtHalf :
  (r : ℚ) →
  logistic r half ≡ r * ((+ 1) R./ 4)
logisticAtHalf r =
  solve (r ∷ [])

------------------------------------------------------------------------
-- The same rational value 1/2 can carry different typed roles.
------------------------------------------------------------------------

data HalfRole : Set where
  logisticFoldCriticalPoint : HalfRole
  branchingCriticalAvailability : HalfRole
  riemannCriticalRealPart : HalfRole

logisticRoleIsNotBranchingRole :
  logisticFoldCriticalPoint ≡ branchingCriticalAvailability → ⊥
logisticRoleIsNotBranchingRole ()

logisticRoleIsNotRiemannRole :
  logisticFoldCriticalPoint ≡ riemannCriticalRealPart → ⊥
logisticRoleIsNotRiemannRole ()

record LogisticFoldCriticalityBoundary : Set where
  constructor logistic-fold-criticality-boundary
  field
    halfIsUniversalDecisionThreshold : Bool
    halfIsUniversalDecisionThresholdIsFalse :
      halfIsUniversalDecisionThreshold ≡ false
    logisticHalfIdentifiedWithRiemannHalf : Bool
    logisticHalfIdentifiedWithRiemannHalfIsFalse :
      logisticHalfIdentifiedWithRiemannHalf ≡ false
    chaosProvedForAllParameters : Bool
    chaosProvedForAllParametersIsFalse :
      chaosProvedForAllParameters ≡ false

canonicalLogisticFoldCriticalityBoundary : LogisticFoldCriticalityBoundary
canonicalLogisticFoldCriticalityBoundary =
  logistic-fold-criticality-boundary
    false refl
    false refl
    false refl
