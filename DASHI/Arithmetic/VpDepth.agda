module DASHI.Arithmetic.VpDepth where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (NonZero)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.DivMod using (_/_; +-distrib-/-∣ˡ)
open import Data.Nat.Divisibility using (_∣?_; _∣_; ∣m+n∣m⇒∣n; ∣m∣n⇒∣m+n)
open import Data.Nat.Divisibility.Core using (divides)
open import Data.Nat.Properties using (+-comm; +-identityʳ; +-suc; ≤-refl; ≤-trans)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Relation.Nullary.Decidable.Core using (yes; no)

------------------------------------------------------------------------
-- Bounded depth valuation on Nat.
--
-- This is a total, fuel-bounded p-adic depth approximation. We treat
-- `0` and `1` as non-prime addresses so recursion cannot stutter on
-- degenerate divisors.

_≢_ : Nat → Nat → Set
x ≢ y = x ≡ y → ⊥

minNat : Nat → Nat → Nat
minNat zero n = zero
minNat (suc m) zero = zero
minNat (suc m) (suc n) = suc (minNat m n)

vp-depth : Nat → Nat → Nat → Nat
vp-depth zero p n = zero
vp-depth (suc fuel) zero n = zero
vp-depth (suc fuel) (suc zero) n = zero
vp-depth (suc fuel) (suc (suc p)) n with suc (suc p) ∣? n
... | yes _ = suc (vp-depth fuel (suc (suc p)) (n / suc (suc p)))
... | no _ = zero

------------------------------------------------------------------------
-- Local helpers for the unequal-valuation theorem.

suc-neq : ∀ {m n} → suc m ≢ suc n → m ≢ n
suc-neq neq eq = neq (cong suc eq)

suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

zero-neq-suc : ∀ {n} → zero ≢ suc n
zero-neq-suc ()

swap-divides-sum :
  ∀ d x y →
  d ∣ (x + y) →
  d ∣ (y + x)
swap-divides-sum d x y d∣x+y =
  divides (_∣_.quotient d∣x+y)
    (trans (+-comm y x) (_∣_.equality d∣x+y))

------------------------------------------------------------------------
-- Fuel behavior.
--
-- The bounded valuation is monotone in fuel, and once one extra unit of
-- fuel stops changing the value, the next unit does not change it either.

vp-depth-monotone-step :
  ∀ fuel p n →
  vp-depth fuel p n ≤ vp-depth (suc fuel) p n
vp-depth-monotone-step zero p n = z≤n
vp-depth-monotone-step (suc fuel) zero n = ≤-refl
vp-depth-monotone-step (suc fuel) (suc zero) n = ≤-refl
vp-depth-monotone-step (suc fuel) (suc (suc p)) n with suc (suc p) ∣? n
... | no _ = ≤-refl
... | yes _ = s≤s (vp-depth-monotone-step fuel (suc (suc p)) (n / suc (suc p)))

vp-depth-monotone :
  ∀ fuel extra p n →
  vp-depth fuel p n ≤ vp-depth (fuel + extra) p n
vp-depth-monotone fuel zero p n rewrite +-identityʳ fuel = ≤-refl
vp-depth-monotone fuel (suc extra) p n
  rewrite +-suc fuel extra =
    ≤-trans
      (vp-depth-monotone fuel extra p n)
      (vp-depth-monotone-step (fuel + extra) p n)

vp-depth-stable-step :
  ∀ fuel p n →
  vp-depth fuel p n ≡ vp-depth (suc fuel) p n →
  vp-depth (suc fuel) p n ≡ vp-depth (suc (suc fuel)) p n
vp-depth-stable-step zero zero n _ = refl
vp-depth-stable-step zero (suc zero) n _ = refl
vp-depth-stable-step zero (suc (suc p)) n eq with suc (suc p) ∣? n
... | no _ = refl
... | yes _ = ⊥-elim (zero-neq-suc eq)
vp-depth-stable-step (suc fuel) zero n _ = refl
vp-depth-stable-step (suc fuel) (suc zero) n _ = refl
vp-depth-stable-step (suc fuel) (suc (suc p)) n eq with suc (suc p) ∣? n
... | no _ = refl
... | yes _ =
  cong suc
    (vp-depth-stable-step
      fuel
      (suc (suc p))
      (n / suc (suc p))
      (suc-injective eq))

vp-depth-stable-next :
  ∀ fuel p n →
  vp-depth (suc fuel) p n ≡ vp-depth (suc (suc fuel)) p n →
  vp-depth (suc (suc fuel)) p n ≡ vp-depth (suc (suc (suc fuel))) p n
vp-depth-stable-next fuel p n =
  vp-depth-stable-step (suc fuel) p n

------------------------------------------------------------------------
-- Depth-level unequal-valuation theorem.

vp-depth-add-min-unequal :
  ∀ fuel p x y →
  vp-depth fuel p x ≢ vp-depth fuel p y →
  vp-depth fuel p (x + y) ≡
  minNat (vp-depth fuel p x) (vp-depth fuel p y)
vp-depth-add-min-unequal zero p x y neq = ⊥-elim (neq refl)
vp-depth-add-min-unequal (suc fuel) zero x y neq = ⊥-elim (neq refl)
vp-depth-add-min-unequal (suc fuel) (suc zero) x y neq = ⊥-elim (neq refl)
vp-depth-add-min-unequal (suc fuel) (suc (suc p)) x y neq
  with suc (suc p) ∣? x | suc (suc p) ∣? y | suc (suc p) ∣? (x + y)
... | no x∤ | no y∤ | yes sumDiv = ⊥-elim (neq refl)
... | no x∤ | no y∤ | no sum∤ = ⊥-elim (neq refl)
... | yes xDiv | no y∤ | yes sumDiv =
  ⊥-elim (y∤ (∣m+n∣m⇒∣n sumDiv xDiv))
... | yes xDiv | no y∤ | no sum∤ = refl
... | no x∤ | yes yDiv | yes sumDiv =
  ⊥-elim (x∤ (∣m+n∣m⇒∣n (swap-divides-sum (suc (suc p)) x y sumDiv) yDiv))
... | no x∤ | yes yDiv | no sum∤ = refl
... | yes xDiv | yes yDiv | no sum∤ =
  ⊥-elim (sum∤ (∣m∣n⇒∣m+n xDiv yDiv))
... | yes xDiv | yes yDiv | yes sumDiv
  rewrite +-distrib-/-∣ˡ {m = x} y xDiv
  = cong suc
      (vp-depth-add-min-unequal
        fuel
        (suc (suc p))
        (x / suc (suc p))
        (y / suc (suc p))
        (suc-neq neq))
