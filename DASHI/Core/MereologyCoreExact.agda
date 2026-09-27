{-# OPTIONS --safe #-}
module DASHI.Core.MereologyCoreExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Set₁)

------------------------------------------------------------------------
-- DOMAIN-NEUTRAL MEREOLOGY CORE
--
-- The carrier deliberately separates:
--   part-of,
--   overlap,
--   compatibility,
--   fusion/reconstruction,
--   same-whole identity,
--   and consumer observation.
--
-- No field is derivable from another merely by sharing a carrier.
------------------------------------------------------------------------

record MereologyCore : Set₁ where
  field
    Part Whole Family Consumer Observation : Set

    partOf :
      Part → Whole → Set

    overlap :
      Part → Part → Set

    compatible :
      Part → Part → Set

    member :
      Part → Family → Set

    fuse :
      Family → Whole

    sameWhole :
      Whole → Whole → Set

    observe :
      Consumer → Whole → Observation

open MereologyCore public

record MereologyNonCollapseBoundary : Set where
  constructor mereology-noncollapse-boundary
  field
    partOfIsSubclassByDefinition : Bool
    partOfIsSubclassByDefinitionIsFalse :
      partOfIsSubclassByDefinition ≡ false

    partOfIsInstanceByDefinition : Bool
    partOfIsInstanceByDefinitionIsFalse :
      partOfIsInstanceByDefinition ≡ false

    overlapCreatesCompatibility : Bool
    overlapCreatesCompatibilityIsFalse :
      overlapCreatesCompatibility ≡ false

    localPartIdentityCreatesWholeIdentity : Bool
    localPartIdentityCreatesWholeIdentityIsFalse :
      localPartIdentityCreatesWholeIdentity ≡ false

    equalObservationCreatesWholeIdentity : Bool
    equalObservationCreatesWholeIdentityIsFalse :
      equalObservationCreatesWholeIdentity ≡ false

canonicalMereologyNonCollapseBoundary : MereologyNonCollapseBoundary
canonicalMereologyNonCollapseBoundary =
  mereology-noncollapse-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
