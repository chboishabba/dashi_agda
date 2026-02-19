module Dashi.ContractiveProjectionDemo where

open import Agda.Builtin.Nat      using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Nullary      using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)
open import Data.Nat              using (_<_)
open import Data.Nat.Properties   as NatP using (z≤n; s≤s)

open import Ultrametric
open import Contraction

------------------------------------------------------------------------
-- Discrete ultrametric on Nat: d x y = 0 if x=y else 1
------------------------------------------------------------------------

_≟_ : Nat → Nat → Dec (Nat)
_≟_ = NatP._≟_

dNat : Nat → Nat → Nat
dNat x y with NatP._≟_ x y
... | yes _ = 0
... | no  _ = 1

id-zeroNat : ∀ x → dNat x x ≡ 0
id-zeroNat x with NatP._≟_ x x
... | yes _ = refl
... | no  n = NatP.⊥-elim (n refl)

symNat : ∀ x y → dNat x y ≡ dNat y x
symNat x y with NatP._≟_ x y | NatP._≟_ y x
... | yes xy | yes yx = refl
... | no  xy | no  yx = refl
... | yes xy | no  yx = NatP.⊥-elim (yx (sym xy))
... | no  xy | yes yx = NatP.⊥-elim (xy (sym yx))

-- ultratriangle: d x z ≤ max (d x y) (d y z)
-- for discrete metric this holds by case split
ultraNat : ∀ x y z → dNat x z NatP.≤ NatP.max (dNat x y) (dNat y z)
ultraNat x y z with NatP._≟_ x z
... | yes _ = z≤n
... | no  x≢z =
  -- then dNat x z = 1, so need 1 ≤ max(...)
  -- If both dNat x y and dNat y z were 0, then x=y and y=z ⇒ x=z contradiction.
  -- So max(...) = 1 and 1 ≤ 1.
  NatP.s≤s z≤n

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

_≢_ : Nat → Nat → Set
x ≢ y = ¬ (x ≡ y)

------------------------------------------------------------------------
-- Strict contraction on distinct points (Contractive≢ style)
------------------------------------------------------------------------

zero<one : 0 < 1
zero<one = s≤s z≤n

contractive≢-proj : ∀ t → (∀ {x y} → x ≢ y → dNat (Kproj t x) (Kproj t y) < dNat x y)
contractive≢-proj t {x} {y} x≢y =
  -- dNat (t) (t) = 0, and if x≢y then dNat x y = 1
  -- so 0 < 1
  zero<one

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
