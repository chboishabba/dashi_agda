module DASHI.Mathematics.NumberTheory.GradedFamilyPointingResidualExact where

------------------------------------------------------------------------
-- GRADED-FAMILY POINTING / RESIDUAL EQUIVALENCE
--
-- The per-object pointing theorem says a grade-n multiplicity object carries
-- exactly n weighted cells.  Deletion/reinsertion, however, naturally acts on
-- the total family of pointed grade-n objects.  This owner extracts that second
-- level without requiring equality of proof-bearing object records.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (Σ; _,_)

------------------------------------------------------------------------
-- A family of grade-indexed objects with a dependent pointed-cell type.

record GradedPointingFamily : Set₁ where
  field
    Object : Nat → Set
    Cell : {n : Nat} → Object n → Set

open GradedPointingFamily public

PointedObject :
  (family : GradedPointingFamily) → Nat → Set
PointedObject family n =
  Σ (Object family n) (λ object → Cell family object)

------------------------------------------------------------------------
-- Exact residual equivalence on the whole grade-n family.
--
-- Residual may retain generator/copy/unit coordinates or any other exact
-- decomposition.  No quotient or extensionality principle is hidden here:
-- domains supply literal maps and round trips at the chosen carrier level.

record GradedFamilyResidualDecomposition
    (family : GradedPointingFamily) : Set₁ where
  field
    Residual : Nat → Set
    delete : {n : Nat} → PointedObject family n → Residual n
    insert : {n : Nat} → Residual n → PointedObject family n
    deleteInsert :
      {n : Nat} → (residual : Residual n) →
      delete (insert residual) ≡ residual
    insertDelete :
      {n : Nat} → (pointed : PointedObject family n) →
      insert (delete pointed) ≡ pointed

open GradedFamilyResidualDecomposition public

------------------------------------------------------------------------
-- This is the finite combinatorial analogue of a pointing/derivative
-- decomposition.  Generating functions, formal derivatives and analytic
-- convergence are intentionally absent from this owner.
------------------------------------------------------------------------
