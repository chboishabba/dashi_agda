module DASHI.Mathematics.NumberTheory.GradedFamilyPointingResidualExact where

------------------------------------------------------------------------
-- GRADED-FAMILY POINTING / RESIDUAL EQUIVALENCE
--
-- The per-object pointing theorem says a grade-n multiplicity object carries
-- exactly n weighted cells.  Deletion/reinsertion, however, naturally acts on
-- the total family of pointed grade-n objects.  This owner extracts that second
-- level and distinguishes literal equality from domain-chosen extensional
-- equality for proof-bearing carriers.
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
-- Literal residual equivalence.

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
-- Extensional residual equivalence.
--
-- Many constructive carriers contain proof fields (mass equalities,
-- positivity witnesses, decomposition equations).  Counting and reindexing
-- should not require equality of those proofs.  A domain may therefore state
-- exactly which data determine the pointed object and residual and prove the
-- two round trips with respect to those relations.
------------------------------------------------------------------------

record ExtensionalGradedFamilyResidualDecomposition
    (family : GradedPointingFamily) : Set₁ where
  field
    Residual : Nat → Set

    PointedEquivalent :
      {n : Nat} →
      PointedObject family n → PointedObject family n → Set

    ResidualEquivalent :
      {n : Nat} → Residual n → Residual n → Set

    pointedReflexive :
      {n : Nat} → (pointed : PointedObject family n) →
      PointedEquivalent pointed pointed

    residualReflexive :
      {n : Nat} → (residual : Residual n) →
      ResidualEquivalent residual residual

    delete : {n : Nat} → PointedObject family n → Residual n
    insert : {n : Nat} → Residual n → PointedObject family n

    deleteInsert :
      {n : Nat} → (residual : Residual n) →
      ResidualEquivalent (delete (insert residual)) residual

    insertDelete :
      {n : Nat} → (pointed : PointedObject family n) →
      PointedEquivalent (insert (delete pointed)) pointed

open ExtensionalGradedFamilyResidualDecomposition public

------------------------------------------------------------------------
-- Literal equality is a special case of the extensional interface.
------------------------------------------------------------------------

literalAsExtensional :
  (family : GradedPointingFamily) →
  GradedFamilyResidualDecomposition family →
  ExtensionalGradedFamilyResidualDecomposition family
literalAsExtensional family decomposition = record
  { Residual = GradedFamilyResidualDecomposition.Residual decomposition
  ; PointedEquivalent = _≡_
  ; ResidualEquivalent = _≡_
  ; pointedReflexive = λ _ → Agda.Builtin.Equality.refl
  ; residualReflexive = λ _ → Agda.Builtin.Equality.refl
  ; delete = GradedFamilyResidualDecomposition.delete decomposition
  ; insert = GradedFamilyResidualDecomposition.insert decomposition
  ; deleteInsert = GradedFamilyResidualDecomposition.deleteInsert decomposition
  ; insertDelete = GradedFamilyResidualDecomposition.insertDelete decomposition
  }

------------------------------------------------------------------------
-- This is the finite combinatorial analogue of a pointing/derivative
-- decomposition.  Generating functions, formal derivatives and analytic
-- convergence are intentionally absent from this owner.
------------------------------------------------------------------------
