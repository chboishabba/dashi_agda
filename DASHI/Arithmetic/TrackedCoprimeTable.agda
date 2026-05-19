module DASHI.Arithmetic.TrackedCoprimeTable where

open import Agda.Builtin.Nat using (Nat)
open import Relation.Nullary using
  ( Dec
  ; yes
  ; no
  )
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Coprimality using
  ( Coprime
  ; gcd≡1⇒coprime
  )
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.TrackedPrimes using
  ( SSP
  ; toNat
  ; _≟_
  ; p2 ; p3 ; p5 ; p7 ; p11 ; p13 ; p17 ; p19 ; p23 ; p29 ; p31 ; p41 ; p47 ; p59 ; p71
  )

------------------------------------------------------------------------
-- Canonical tracked-base coprime evidence.
--
-- The tracked carrier itself already lives in DASHI.TrackedPrimes. This
-- module centralises the finite coprimality table so downstream arithmetic
-- modules can consume one theorem instead of carrying a 15x15 clause block.

_≢_ : SSP → SSP → Set
p ≢ q = p ≡ q → ⊥

gcdTable : SSP → SSP → Nat
gcdTable p q with p ≟ q
... | yes _ = toNat p
... | no _  = 1

gcdTable-distinct :
  ∀ p q →
  p ≢ q →
  gcdTable p q ≡ 1
gcdTable-distinct p q p≢q with p ≟ q
... | yes p≡q = ⊥-elim (p≢q p≡q)
... | no _    = refl

distinctTrackedBasesCoprime :
  ∀ p q →
  p ≢ q →
  Coprime (toNat p) (toNat q)
distinctTrackedBasesCoprime p2 p2 p≢q = ⊥-elim (p≢q refl)
distinctTrackedBasesCoprime p2 p3 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p2 p5 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p2 p7 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p2 p11 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p2 p13 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p2 p17 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p2 p19 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p2 p23 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p2 p29 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p2 p31 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p2 p41 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p2 p47 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p2 p59 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p2 p71 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p3 p2 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p3 p3 p≢q = ⊥-elim (p≢q refl)
distinctTrackedBasesCoprime p3 p5 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p3 p7 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p3 p11 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p3 p13 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p3 p17 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p3 p19 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p3 p23 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p3 p29 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p3 p31 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p3 p41 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p3 p47 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p3 p59 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p3 p71 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p5 p2 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p5 p3 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p5 p5 p≢q = ⊥-elim (p≢q refl)
distinctTrackedBasesCoprime p5 p7 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p5 p11 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p5 p13 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p5 p17 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p5 p19 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p5 p23 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p5 p29 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p5 p31 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p5 p41 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p5 p47 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p5 p59 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p5 p71 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p7 p2 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p7 p3 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p7 p5 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p7 p7 p≢q = ⊥-elim (p≢q refl)
distinctTrackedBasesCoprime p7 p11 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p7 p13 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p7 p17 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p7 p19 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p7 p23 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p7 p29 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p7 p31 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p7 p41 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p7 p47 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p7 p59 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p7 p71 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p11 p2 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p11 p3 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p11 p5 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p11 p7 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p11 p11 p≢q = ⊥-elim (p≢q refl)
distinctTrackedBasesCoprime p11 p13 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p11 p17 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p11 p19 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p11 p23 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p11 p29 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p11 p31 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p11 p41 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p11 p47 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p11 p59 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p11 p71 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p13 p2 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p13 p3 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p13 p5 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p13 p7 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p13 p11 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p13 p13 p≢q = ⊥-elim (p≢q refl)
distinctTrackedBasesCoprime p13 p17 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p13 p19 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p13 p23 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p13 p29 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p13 p31 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p13 p41 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p13 p47 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p13 p59 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p13 p71 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p17 p2 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p17 p3 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p17 p5 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p17 p7 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p17 p11 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p17 p13 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p17 p17 p≢q = ⊥-elim (p≢q refl)
distinctTrackedBasesCoprime p17 p19 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p17 p23 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p17 p29 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p17 p31 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p17 p41 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p17 p47 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p17 p59 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p17 p71 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p19 p2 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p19 p3 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p19 p5 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p19 p7 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p19 p11 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p19 p13 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p19 p17 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p19 p19 p≢q = ⊥-elim (p≢q refl)
distinctTrackedBasesCoprime p19 p23 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p19 p29 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p19 p31 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p19 p41 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p19 p47 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p19 p59 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p19 p71 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p23 p2 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p23 p3 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p23 p5 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p23 p7 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p23 p11 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p23 p13 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p23 p17 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p23 p19 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p23 p23 p≢q = ⊥-elim (p≢q refl)
distinctTrackedBasesCoprime p23 p29 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p23 p31 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p23 p41 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p23 p47 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p23 p59 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p23 p71 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p29 p2 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p29 p3 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p29 p5 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p29 p7 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p29 p11 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p29 p13 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p29 p17 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p29 p19 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p29 p23 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p29 p29 p≢q = ⊥-elim (p≢q refl)
distinctTrackedBasesCoprime p29 p31 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p29 p41 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p29 p47 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p29 p59 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p29 p71 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p31 p2 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p31 p3 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p31 p5 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p31 p7 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p31 p11 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p31 p13 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p31 p17 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p31 p19 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p31 p23 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p31 p29 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p31 p31 p≢q = ⊥-elim (p≢q refl)
distinctTrackedBasesCoprime p31 p41 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p31 p47 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p31 p59 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p31 p71 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p41 p2 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p41 p3 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p41 p5 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p41 p7 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p41 p11 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p41 p13 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p41 p17 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p41 p19 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p41 p23 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p41 p29 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p41 p31 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p41 p41 p≢q = ⊥-elim (p≢q refl)
distinctTrackedBasesCoprime p41 p47 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p41 p59 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p41 p71 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p47 p2 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p47 p3 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p47 p5 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p47 p7 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p47 p11 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p47 p13 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p47 p17 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p47 p19 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p47 p23 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p47 p29 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p47 p31 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p47 p41 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p47 p47 p≢q = ⊥-elim (p≢q refl)
distinctTrackedBasesCoprime p47 p59 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p47 p71 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p59 p2 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p59 p3 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p59 p5 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p59 p7 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p59 p11 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p59 p13 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p59 p17 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p59 p19 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p59 p23 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p59 p29 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p59 p31 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p59 p41 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p59 p47 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p59 p59 p≢q = ⊥-elim (p≢q refl)
distinctTrackedBasesCoprime p59 p71 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p71 p2 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p71 p3 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p71 p5 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p71 p7 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p71 p11 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p71 p13 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p71 p17 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p71 p19 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p71 p23 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p71 p29 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p71 p31 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p71 p41 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p71 p47 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p71 p59 _ = gcd≡1⇒coprime refl
distinctTrackedBasesCoprime p71 p71 p≢q = ⊥-elim (p≢q refl)
