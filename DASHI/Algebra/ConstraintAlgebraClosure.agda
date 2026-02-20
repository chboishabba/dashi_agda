module DASHI.Algebra.ConstraintAlgebraClosure where

open import DASHI.Algebra.ConstraintAlgebraClosureTests renaming
  (DiracClosure to DiracClosureType
  ; ValuationEquivariance to ValuationEquivarianceType
  ; NoLeakageStability to NoLeakageStabilityType
  ; ConstraintAlgebraTheorem to ConstraintAlgebraTheoremType)

record ConstraintClosureBundle : Set₁ where
  field
    invariance : ValuationEquivarianceType
    stability : NoLeakageStabilityType

closure-from-bundle : ConstraintClosureBundle → DiracClosureType
closure-from-bundle bundle =
  ConstraintAlgebraTheoremType
    (ConstraintClosureBundle.invariance bundle)
    (ConstraintClosureBundle.stability bundle)

record ConstraintConsequences (bundle : ConstraintClosureBundle) : Set₁ where
  field
    closure : DiracClosureType

ConstraintClosure-theorem : ConstraintClosureBundle → DiracClosureType
ConstraintClosure-theorem = closure-from-bundle
