module Ontology.Hecke.SignedTransport where

open import Agda.Builtin.Bool     using (Bool)
open import Agda.Builtin.Maybe    using (Maybe; just; nothing)
open import Agda.Builtin.Nat      using (Nat)
open import Agda.Builtin.Equality using (_≡_)

open import MonsterOntos using (SSP)
open import Ontology.GodelLattice using (FactorVec)

------------------------------------------------------------------------
-- Signed transport is the next step beyond pure exponent bumping:
-- moves may fail when a decrement is illegal, and successful moves carry a
-- reverse-Hecke discrepancy on the same prime-address carrier.

record SignedTransportOn (S : Set) : Set₁ where
  field
    transport   : SSP → S → Maybe S
    legal       : SSP → S → Bool

record SignedReverseHeckeOn (S : Set) : Set₁ where
  field
    address       : S → FactorVec
    transport     : SSP → S → Maybe S
    pullback      : SSP → FactorVec → Maybe FactorVec
    discrepancy   : SSP → S → Nat
    legal         : SSP → S → Bool

    compatible-sound :
      ∀ p s s' →
      transport p s ≡ just s' →
      pullback p (address s) ≡ just (address s')
