module Ontology.Hecke.ReverseRepresentation where

open import Agda.Builtin.Bool     using (Bool; true)
open import Agda.Builtin.Nat      using (Nat)
open import Agda.Builtin.Equality using (_≡_)

open import MonsterOntos          using (SSP)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.Hecke.Scan   using
  (State; HeckeFamily; HeckeFamilyOn; Sig15; scan; scanOn)

------------------------------------------------------------------------
-- Reverse Hecke lives on the representation layer:
-- transport in a state family is compared against a pullback on the
-- prime-factor address. The discrepancy is the reverse-side metric.

record ReverseHeckeMetricOn (S : Set) : Set₁ where
  field
    address     : S → FactorVec
    transport   : SSP → S → S
    pullback    : SSP → FactorVec → FactorVec
    discrepancy : SSP → S → Nat
    compatible  : SSP → S → Bool

    compatible-sound :
      ∀ p s →
      compatible p s ≡ true →
      address (transport p s) ≡ pullback p (address s)

  reverseHecke : HeckeFamilyOn S
  reverseHecke = record
    { T      = transport
    ; compat = compatible
    }

  signature : S → Sig15
  signature = scanOn reverseHecke

record ReverseHeckeMetric : Set₁ where
  field
    address     : State → FactorVec
    transport   : SSP → State → State
    pullback    : SSP → FactorVec → FactorVec
    discrepancy : SSP → State → Nat
    compatible  : SSP → State → Bool

    compatible-sound :
      ∀ p s →
      compatible p s ≡ true →
      address (transport p s) ≡ pullback p (address s)

  reverseHecke : HeckeFamily
  reverseHecke = record
    { T      = transport
    ; compat = compatible
    }

  signature : State → Sig15
  signature = scan reverseHecke
