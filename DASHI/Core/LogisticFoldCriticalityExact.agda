module DASHI.Core.LogisticFoldCriticalityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Robert M. May,
-- "Simple mathematical models with very complicated dynamics",
-- Nature 261 (1976), 459--467.
-- DOI: 10.1038/261459a0.
--
-- REPOSITORY AUTHORITY
--
-- DASHI.Dynamics.LogisticAdicStageCommutingSpine already owns the generic
-- algebraic logistic step
--
--   L_r(x) = r*x*(1-x)
--
-- together with chart-separation and morphism-commutation machinery.  This
-- module therefore does NOT define a second logistic map.  It instantiates the
-- merged owner at the rational algebra and proves the elementary x=1/2 fold
-- facts required by the number-role/provenance tranche.
--
-- No claim is made here about a specific chaotic parameter, Lyapunov exponent,
-- empirical decision threshold, or identification with the RH critical line.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)
open import Data.Integer using (+_)
open import Data.Rational as R using (_/_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Dynamics.LogisticAdicStageCommutingSpine as Spine

half : ℚ
half = (+ 1) R./ 2

------------------------------------------------------------------------
-- Rational instance of the already-merged generic logistic algebra.
------------------------------------------------------------------------

rationalLogisticAlgebra : Spine.LogisticAlgebra ℚ
rationalLogisticAlgebra = record
  { one = 1ℚ
  ; sub = _-_
  ; mul = _*_
  }

logistic : ℚ → ℚ → ℚ
logistic = Spine.logisticStep rationalLogisticAlgebra

logisticIsMergedSpineStep :
  (r x : ℚ) →
  logistic r x ≡ Spine.logisticStep rationalLogisticAlgebra r x
logisticIsMergedSpineStep r x = refl

------------------------------------------------------------------------
-- Formal derivative and fold facts for the rational chart.
------------------------------------------------------------------------

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
    secondLogisticOwnerIntroducedHere : Bool
    secondLogisticOwnerIntroducedHereIsFalse :
      secondLogisticOwnerIntroducedHere ≡ false
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
    false refl
