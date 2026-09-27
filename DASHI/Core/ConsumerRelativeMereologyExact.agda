{-# OPTIONS --safe #-}
module DASHI.Core.ConsumerRelativeMereologyExact where

open import Agda.Builtin.Equality using (_≡_)

------------------------------------------------------------------------
-- CONSUMER-RELATIVE MEREOLOGY
--
-- A consumer is allowed to require only a projection of a whole.  Adequacy
-- for that consumer is therefore weaker than same-whole identity unless an
-- explicit reflection theorem is supplied.
------------------------------------------------------------------------

record ConsumerProjection : Set₁ where
  field
    Whole Consumer Observation : Set

    project :
      Consumer → Whole → Observation

    SameWhole :
      Whole → Whole → Set

open ConsumerProjection public

ConsumerEquivalent :
  (P : ConsumerProjection) →
  Consumer P →
  Whole P →
  Whole P →
  Set
ConsumerEquivalent P c x y =
  project P c x ≡ project P c y

record ProjectionReflectsWhole
    (P : ConsumerProjection)
    (c : Consumer P) : Set₁ where
  field
    reflect :
      ∀ x y →
      ConsumerEquivalent P c x y →
      SameWhole P x y

open ProjectionReflectsWhole public

sameWholeFromConsumerObservation :
  ∀ (P : ConsumerProjection)
    (c : Consumer P) →
  ProjectionReflectsWhole P c →
  ∀ x y →
  ConsumerEquivalent P c x y →
  SameWhole P x y
sameWholeFromConsumerObservation P c reflection x y eq =
  reflect reflection x y eq

------------------------------------------------------------------------
-- Minimal-part-family surface for a declared consumer.
------------------------------------------------------------------------

record ConsumerPartFamily : Set₁ where
  field
    Part Family Consumer : Set

    Required :
      Consumer → Part → Set

    member :
      Part → Family → Set

    Covers :
      Consumer → Family → Set

    coversSound :
      ∀ c family part →
      Required c part →
      Covers c family →
      member part family

open ConsumerPartFamily public
