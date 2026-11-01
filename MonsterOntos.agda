module MonsterOntos where

open import Agda.Builtin.Nat      using (Nat; zero; suc)
open import Agda.Builtin.Bool     using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)
open import Data.Nat.Properties renaming (_≟_ to nat≟)

------------------------------------------------------------------------
-- Ontos: the 15 supersingular primes used as the base carrier.

data SSP : Set where
  p2  : SSP
  p3  : SSP
  p5  : SSP
  p7  : SSP
  p11 : SSP
  p13 : SSP
  p17 : SSP
  p19 : SSP
  p23 : SSP
  p29 : SSP
  p31 : SSP
  p41 : SSP
  p47 : SSP
  p59 : SSP
  p71 : SSP

------------------------------------------------------------------------
-- A concrete embedding to Nat (for mod/sharding etc).

toNat : SSP → Nat
toNat p2  = 2
toNat p3  = 3
toNat p5  = 5
toNat p7  = 7
toNat p11 = 11
toNat p13 = 13
toNat p17 = 17
toNat p19 = 19
toNat p23 = 23
toNat p29 = 29
toNat p31 = 31
toNat p41 = 41
toNat p47 = 47
toNat p59 = 59
toNat p71 = 71

------------------------------------------------------------------------
-- toNat is injective because each prime maps to a unique Nat

toNat-injective : ∀ {p q} → toNat p ≡ toNat q → p ≡ q
toNat-injective {p = p2}  {q = p2}  refl = refl
toNat-injective {p = p3}  {q = p3}  refl = refl
toNat-injective {p = p5}  {q = p5}  refl = refl
toNat-injective {p = p7}  {q = p7}  refl = refl
toNat-injective {p = p11} {q = p11} refl = refl
toNat-injective {p = p13} {q = p13} refl = refl
toNat-injective {p = p17} {q = p17} refl = refl
toNat-injective {p = p19} {q = p19} refl = refl
toNat-injective {p = p23} {q = p23} refl = refl
toNat-injective {p = p29} {q = p29} refl = refl
toNat-injective {p = p31} {q = p31} refl = refl
toNat-injective {p = p41} {q = p41} refl = refl
toNat-injective {p = p47} {q = p47} refl = refl
toNat-injective {p = p59} {q = p59} refl = refl
toNat-injective {p = p71} {q = p71} refl = refl

------------------------------------------------------------------------
-- Decide equality by comparing the embedded Nat values

_≟_ : (p q : SSP) → Dec (p ≡ q)
_≟_ p q with nat≟ (toNat p) (toNat q)
... | yes eq   = yes (toNat-injective eq)
... | no contra = no (λ eq → contra (cong toNat eq))
