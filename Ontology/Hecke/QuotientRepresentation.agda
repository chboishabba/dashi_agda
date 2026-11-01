module Ontology.Hecke.QuotientRepresentation where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma    using (Σ; _,_)

open import MonsterOntos          using (SSP)

------------------------------------------------------------------------
-- Minimal equivalence / quotient interface for Hecke on representation
-- classes. This stays at the interface level and does not assume cubical
-- quotient elimination.

record EquivalenceOn (S : Set) : Set₁ where
  field
    _≈_   : S → S → Set
    refl  : ∀ x → x ≈ x
    sym   : ∀ {x y} → x ≈ y → y ≈ x
    trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

open EquivalenceOn public

record QuotientInterfaceOn (S Class : Set) : Set₁ where
  field
    equiv : EquivalenceOn S
    proj  : S → Class

    respect-proj :
      ∀ {x y} →
      EquivalenceOn._≈_ equiv x y →
      proj x ≡ proj y

    representative : Class → S
    section :
      ∀ c → proj (representative c) ≡ c

  fiber : Class → Set
  fiber c = Σ S (λ s → proj s ≡ c)

record QuotientHeckeActionOn (S Class : Set) : Set₁ where
  field
    quotient : QuotientInterfaceOn S Class
    transport : SSP → S → S
    classHecke : SSP → Class → Class

    respects-equiv :
      ∀ p {x y} →
      EquivalenceOn._≈_ (QuotientInterfaceOn.equiv quotient) x y →
      EquivalenceOn._≈_ (QuotientInterfaceOn.equiv quotient)
        (transport p x) (transport p y)

    class-sound :
      ∀ p x →
      QuotientInterfaceOn.proj quotient (transport p x)
        ≡ classHecke p (QuotientInterfaceOn.proj quotient x)

  fiberHecke : SSP → Class → Class
  fiberHecke = classHecke
