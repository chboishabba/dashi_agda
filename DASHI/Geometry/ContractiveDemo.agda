module DASHI.Geometry.ContractiveDemo where

open import Agda.Builtin.Nat      using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Nullary      using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)
-- Removed Reasoning imports as they are missing in stdlib.
open import Data.Nat              using (_<_; z≤n; s≤s; _≟_; _≤_; _⊔_)
open import Data.Nat.Base         using (z<s)
open import Data.Empty            using (⊥-elim)

open import Ultrametric
open import Contraction

------------------------------------------------------------------------
-- Discrete ultrametric on Nat: d x y = 0 if x=y else 1
------------------------------------------------------------------------

dNat : Nat → Nat → Nat
dNat x y with x ≟ y
... | yes _ = 0
... | no  _ = 1

dNat-refl0 : ∀ t → dNat t t ≡ 0
dNat-refl0 t with t ≟ t
... | yes _ = refl
... | no  n = ⊥-elim (n refl)

id-zeroNat : ∀ x → dNat x x ≡ 0
id-zeroNat x with x ≟ x
... | yes _ = refl
... | no  n = ⊥-elim (n refl)

symNat : ∀ x y → dNat x y ≡ dNat y x
symNat x y with x ≟ y | y ≟ x
... | yes xy | yes yx = refl
... | no  xy | no  yx = refl
... | yes xy | no  yx = ⊥-elim (yx (sym xy))
... | no  xy | yes yx = ⊥-elim (xy (sym yx))

-- ultratriangle: d x z ≤ max (d x y) (d y z)
-- for discrete metric this holds by case split
ultraNat : ∀ x y z → dNat x z ≤ (dNat x y ⊔ dNat y z)
ultraNat x y z with x ≟ z
... | yes _ = z≤n
... | no x≢z with x ≟ y | y ≟ z
...   | yes xy | yes yz = ⊥-elim (x≢z (trans xy yz))
...   | no  _  | yes yz = s≤s z≤n
...   | yes xy | no  _  = s≤s z≤n
...   | no  _  | no  _  = s≤s z≤n

UNat : Ultrametric Nat
UNat = record
  { d             = dNat
  ; id-zero       = id-zeroNat
  ; symmetric     = symNat
  ; ultratriangle = ultraNat
  }

------------------------------------------------------------------------
-- A projection operator: K projects everything to a fixed target t
------------------------------------------------------------------------

Kproj : Nat → Nat → Nat
Kproj t _ = t

------------------------------------------------------------------------
-- Distinctness helper
------------------------------------------------------------------------

dNat-x≢y=1 : ∀ {x y} → x ≢ y → dNat x y ≡ 1
dNat-x≢y=1 {x} {y} x≢y with x ≟ y
... | yes eq = ⊥-elim (x≢y eq)
... | no _ = refl

------------------------------------------------------------------------
-- Strict contraction on distinct points (Contractive≢ style)
------------------------------------------------------------------------

contractive≢-proj : ∀ t → (∀ {x y} → x ≢ y → dNat (Kproj t x) (Kproj t y) < dNat x y)
contractive≢-proj t {x} {y} x≢y
  rewrite dNat-refl0 t
        | dNat-x≢y=1 {x} {y} x≢y
  = z<s

------------------------------------------------------------------------
-- Fixed point uniqueness for projection
------------------------------------------------------------------------

Fixed : (Nat → Nat) → Nat → Set
Fixed K a = K a ≡ a

uniqueFixedProj :
  ∀ t x y →
  Fixed (Kproj t) x →
  Fixed (Kproj t) y →
  x ≡ y
uniqueFixedProj t x y fx fy =
  trans (sym fx) fy
