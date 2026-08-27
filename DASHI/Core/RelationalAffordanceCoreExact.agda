module DASHI.Core.RelationalAffordanceCoreExact where

------------------------------------------------------------------------
-- RELATIONAL AFFORDANCE CORE
--
-- SOURCE CALIBRATION
-- James J. Gibson, The Ecological Approach to Visual Perception,
-- Houghton Mifflin, 1979; later Psychology Press/Routledge editions.
-- ISBN 9781848725782 (2015 classic edition). No DOI asserted for the book.
--
-- Gibson motivates affordance as an organism/environment relation. The exact
-- type-theoretic factorisation and non-promotion boundaries below are DASHI
-- constructions, not claims that Gibson supplied this formal calculus.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record AffordanceEcology : Set₁ where
  constructor affordance-ecology
  field
    Person : Set
    Environment : Set
    Action : Set
    Afforded : Person → Environment → Action → Set
    Perceived : Person → Environment → Action → Set
    Accessible : Person → Environment → Action → Set
    Realized : Person → Environment → Action → Set

open AffordanceEcology public

record AffordanceWitness (ecology : AffordanceEcology) : Set₁ where
  constructor affordance-witness
  field
    person : Person ecology
    environment : Environment ecology
    action : Action ecology
    afforded : Afforded ecology person environment action

open AffordanceWitness public

record AffordanceTransitionEvidence (ecology : AffordanceEcology) : Set₁ where
  constructor affordance-transition-evidence
  field
    affordanceToPerception :
      (p : Person ecology) → (e : Environment ecology) → (a : Action ecology) →
      Afforded ecology p e a → Perceived ecology p e a
    perceptionToAccessibility :
      (p : Person ecology) → (e : Environment ecology) → (a : Action ecology) →
      Perceived ecology p e a → Accessible ecology p e a
    accessibilityToRealization :
      (p : Person ecology) → (e : Environment ecology) → (a : Action ecology) →
      Accessible ecology p e a → Realized ecology p e a

record RelationalAffordanceBoundary : Set where
  constructor relational-affordance-boundary
  field
    environmentAloneDeterminesAffordance : Bool
    environmentAloneDeterminesAffordanceIsFalse :
      environmentAloneDeterminesAffordance ≡ false
    personAloneDeterminesAffordance : Bool
    personAloneDeterminesAffordanceIsFalse :
      personAloneDeterminesAffordance ≡ false
    affordedAutomaticallyPerceived : Bool
    affordedAutomaticallyPerceivedIsFalse :
      affordedAutomaticallyPerceived ≡ false
    perceivedAutomaticallyAccessible : Bool
    perceivedAutomaticallyAccessibleIsFalse :
      perceivedAutomaticallyAccessible ≡ false
    accessibleAutomaticallyRealized : Bool
    accessibleAutomaticallyRealizedIsFalse :
      accessibleAutomaticallyRealized ≡ false

canonicalRelationalAffordanceBoundary : RelationalAffordanceBoundary
canonicalRelationalAffordanceBoundary =
  relational-affordance-boundary
    false refl false refl false refl false refl false refl
