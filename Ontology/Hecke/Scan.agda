module Ontology.Hecke.Scan where

open import Agda.Builtin.Bool     using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import MonsterOntos

------------------------------------------------------------------------
-- A computational/cognitive state.
postulate
  State : Set

------------------------------------------------------------------------
-- Hecke operator family: T_p : State → State for each p in the ontos.

record HeckeFamilyOn (S : Set) : Set₁ where
  field
    T : SSP → S → S
    compat : SSP → S → Bool

record HeckeFamily : Set₁ where
  field
    T : SSP → State → State
    compat : SSP → State → Bool

------------------------------------------------------------------------
-- A "compatibility detector" is just a predicate you choose.
-- Example: does the state remain invariant under T_p?

CompatOn : ∀ {S : Set} → HeckeFamilyOn S → SSP → S → Bool
CompatOn H = HeckeFamilyOn.compat H

Compat : HeckeFamily → SSP → State → Bool
Compat H = HeckeFamily.compat H

------------------------------------------------------------------------
-- A scan produces a 15-bit signature (compatibility bits across primes).

record Sig15 : Set where
  constructor sig15
  field
    b2  : Bool; b3  : Bool; b5  : Bool; b7  : Bool; b11 : Bool
    b13 : Bool; b17 : Bool; b19 : Bool; b23 : Bool; b29 : Bool
    b31 : Bool; b41 : Bool; b47 : Bool; b59 : Bool; b71 : Bool

scanOn : ∀ {S : Set} → HeckeFamilyOn S → S → Sig15
scanOn H s = sig15
  (CompatOn H p2  s) (CompatOn H p3  s) (CompatOn H p5  s) (CompatOn H p7  s) (CompatOn H p11 s)
  (CompatOn H p13 s) (CompatOn H p17 s) (CompatOn H p19 s) (CompatOn H p23 s) (CompatOn H p29 s)
  (CompatOn H p31 s) (CompatOn H p41 s) (CompatOn H p47 s) (CompatOn H p59 s) (CompatOn H p71 s)

scan : HeckeFamily → State → Sig15
scan H s = sig15
  (Compat H p2  s) (Compat H p3  s) (Compat H p5  s) (Compat H p7  s) (Compat H p11 s)
  (Compat H p13 s) (Compat H p17 s) (Compat H p19 s) (Compat H p23 s) (Compat H p29 s)
  (Compat H p31 s) (Compat H p41 s) (Compat H p47 s) (Compat H p59 s) (Compat H p71 s)
