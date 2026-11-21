{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSVFOriginalArbitraryReflectionCollapseNoGoExact where

------------------------------------------------------------------------
-- HIL07 original source negative control:
--
-- The former M2b requiring
--   ∀ (reflection : Observable → Observable) cylinder →
--     cylinderOperator (reflection cylinder)
--       = adjoint (cylinderOperator cylinder)
-- for *every* function called a reflection is too strong.
--
-- Choose two constant functions reflectionₐ / reflectionᵦ.  The
-- required equations force cylinderOperator a = cylinderOperator b
-- for any observables a and b. Thus an injective/nontrivial selected
-- cylinder representation cannot satisfy the old condition.
--
-- The physical source must pick ONE actual reflection and the
-- associated gauge-invariant positive-time observable algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Data.Empty using (⊥)

module _
    {Observable Operator : Set}
    (cylinderOperator : Observable → Operator)
    (adjoint : Operator → Operator)
    (unphysicalAllReflections :
      (reflection : Observable → Observable) →
      (cylinder : Observable) →
      cylinderOperator (reflection cylinder)
        ≡ adjoint (cylinderOperator cylinder))
  where

  unphysicalAllReflectionsCollapseCylinderRepresentation :
    (left right : Observable) →
    cylinderOperator left ≡ cylinderOperator right
  unphysicalAllReflectionsCollapseCylinderRepresentation left right =
    trans
      (unphysicalAllReflections (λ _ → left) left)
      (sym (unphysicalAllReflections (λ _ → right) left))

  selectedDistinctCylinderImagesRefuteAllReflections :
    (left right : Observable) →
    (cylinderOperator left ≡ cylinderOperator right → ⊥) →
    ⊥
  selectedDistinctCylinderImagesRefuteAllReflections
      left right distinguish =
    distinguish
      (unphysicalAllReflectionsCollapseCylinderRepresentation
        left right)

-- No classifying all maps as true reflections in the repaired
-- source's selectedPhysicalReflection field. This source theorem
-- is a falsifier of an overstrong binder, not a new physical axiom.
