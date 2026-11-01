module DASHI.Algebra.ConstraintAlgebraClosure where

open import DASHI.Algebra.ConstraintAlgebraClosureTests renaming
  (ConstraintAlgebraAxioms to ConstraintAlgebraAxiomsType
  ; DiracClosure to DiracClosureType
  ; ConstraintAlgebraTheorem to ConstraintAlgebraTheoremType)

record ConstraintClosureBundle : Set₁ where
  field
    axioms : ConstraintAlgebraAxiomsType

closure-from-bundle :
  (bundle : ConstraintClosureBundle) →
  DiracClosureType (ConstraintAlgebraAxiomsType.struct (ConstraintClosureBundle.axioms bundle))
closure-from-bundle bundle =
  ConstraintAlgebraTheoremType (ConstraintClosureBundle.axioms bundle)

record ConstraintConsequences (bundle : ConstraintClosureBundle) : Set₁ where
  field
    closure :
      DiracClosureType (ConstraintAlgebraAxiomsType.struct (ConstraintClosureBundle.axioms bundle))

ConstraintClosure-theorem :
  (bundle : ConstraintClosureBundle) →
  DiracClosureType (ConstraintAlgebraAxiomsType.struct (ConstraintClosureBundle.axioms bundle))
ConstraintClosure-theorem = closure-from-bundle
