module MonsterOntos where

open import Agda.Builtin.Nat      using (Nat; zero; suc)
open import Agda.Builtin.Bool     using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

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
-- Decidable equality (hand-rolled; keeps you stdlib-light)

data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : (A → ⊥) → Dec A

data ⊥ : Set where

_≟_ : (p q : SSP) → Dec (p ≡ q)
p2  ≟ p2  = yes refl
p3  ≟ p3  = yes refl
p5  ≟ p5  = yes refl
p7  ≟ p7  = yes refl
p11 ≟ p11 = yes refl
p13 ≟ p13 = yes refl
p17 ≟ p17 = yes refl
p19 ≟ p19 = yes refl
p23 ≟ p23 = yes refl
p29 ≟ p29 = yes refl
p31 ≟ p31 = yes refl
p41 ≟ p41 = yes refl
p47 ≟ p47 = yes refl
p59 ≟ p59 = yes refl
p71 ≟ p71 = yes refl
_   ≟ _   = no (λ ())
