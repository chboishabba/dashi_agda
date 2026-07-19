{-# OPTIONS --safe #-}

module DASHI.Geometry.UniversalCanonicalQuotient where

open import Agda.Builtin.Equality using (_≡_; refl; sym; trans)

------------------------------------------------------------------------
-- A quotient presentation is deliberately independent of a particular
-- implementation of groups, setoids, or algebraic varieties.  The relation
-- may be instantiated by an orbit relation, gauge equivalence, observational
-- equivalence, or a DASHI kernel congruence.
------------------------------------------------------------------------

record QuotientPresentation (X Q : Set) : Set₁ where
  field
    _≈_ : X → X → Set
    π : X → Q
    section : Q → X

    -- Every quotient point has a chosen canonical representative.
    retract : ∀ q → π (section q) ≡ q

    -- Soundness and completeness say that π identifies exactly the intended
    -- equivalence classes.
    sound : ∀ {x y} → x ≈ y → π x ≡ π y
    complete : ∀ {x y} → π x ≡ π y → x ≈ y

    -- Every state is equivalent to its chosen representative.
    canonical : ∀ x → x ≈ section (π x)

open QuotientPresentation public

------------------------------------------------------------------------
-- Invariant maps and factorisations.
------------------------------------------------------------------------

Invariant :
  ∀ {X Q Y : Set} → QuotientPresentation X Q → (X → Y) → Set
Invariant P f = ∀ {x y} → QuotientPresentation._≈_ P x y → f x ≡ f y

record Factorisation
  {X Q Y : Set}
  (π : X → Q)
  (f : X → Y)
  : Set₁ where
  field
    descend : Q → Y
    commutes : ∀ x → descend (π x) ≡ f x

open Factorisation public

record UniqueFactorisation
  {X Q Y : Set}
  (π : X → Q)
  (f : X → Y)
  : Set₁ where
  field
    factorisation : Factorisation π f
    unique :
      ∀ (h : Q → Y) →
      (∀ x → h (π x) ≡ f x) →
      ∀ q → h q ≡ Factorisation.descend factorisation q

open UniqueFactorisation public

------------------------------------------------------------------------
-- Universal quotient theorem.
--
-- Any map constant on equivalence classes factors uniquely through π.
-- No function extensionality is required: uniqueness is pointwise.
------------------------------------------------------------------------

universalCanonicalQuotient :
  ∀ {X Q Y : Set}
  (P : QuotientPresentation X Q)
  (f : X → Y) →
  Invariant P f →
  UniqueFactorisation (QuotientPresentation.π P) f
universalCanonicalQuotient P f invariant = record
  { factorisation = record
      { descend = λ q → f (section P q)
      ; commutes = λ x → invariant (canonical P x)
      }
  ; unique = λ h h-commutes q → uniqueness h h-commutes q
  }
  where
  uniqueness :
    (h : Q → Y) →
    (∀ x → h (π P x) ≡ f x) →
    ∀ q → h q ≡ f (section P q)
  uniqueness h h-commutes q
    rewrite retract P q = h-commutes (section P q)

------------------------------------------------------------------------
-- Canonical-map consequences used by DASHI.
------------------------------------------------------------------------

canonical-idempotent :
  ∀ {X Q : Set}
  (P : QuotientPresentation X Q)
  (x : X) →
  π P (section P (π P x)) ≡ π P x
canonical-idempotent P x = retract P (π P x)

canonical-separates-classes :
  ∀ {X Q : Set}
  (P : QuotientPresentation X Q)
  {x y : X} →
  π P x ≡ π P y →
  x ≈ y
canonical-separates-classes P = complete P
