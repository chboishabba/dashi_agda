module DASHI.Physics.Closure.QuantumCarrierCore where

------------------------------------------------------------------------
-- Lightweight Quantum / Multiscale carrier interface.
-- Decoupled from Unifier.agda monolithic rollups to avoid circular
-- dependencies and excessive import cones in physics and environment.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
import Data.Nat as Nat
open import Data.Nat.Base using (ℕ)
open import Data.Integer.Base using (ℤ)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)

ℝ : Set
ℝ = ℕ

ℂ : Set
ℂ = ℕ

toℝ : ℕ → ℝ
toℝ n = n

_+ℝ_ : ℝ → ℝ → ℝ
_+ℝ_ = Nat._+_

_*ℝ_ : ℝ → ℝ → ℝ
_*ℝ_ = Nat._*_

_-ℝ_ : ℝ → ℝ → ℝ
_-ℝ_ = Nat._∸_

_≤ℝ_ : ℝ → ℝ → Set
_≤ℝ_ = Nat._≤_

maxℝ : ℝ → ℝ → ℝ
maxℝ = Nat._⊔_

_<ℝ_ : ℝ → ℝ → Set
_<ℝ_ = Nat._<_

record Scale : Set where
  constructor mkScale
  field
    ℓ : ℤ

next : Scale → Scale
next s = s

record Tower : Set₁ where
  field
    S   : Scale → Set
    R   : ∀ {ℓ} → S ℓ → S (next ℓ)
    P   : ∀ {ℓ} → S ℓ → S ℓ
    C   : ∀ {ℓ} → S ℓ → S ℓ

record HilbertSpace : Set₁ where
  field
    H : Set
    ⟨_,_⟩ : H → H → ℂ

record WaveLift (Tow : Tower) (HS : HilbertSpace) : Set₁ where
  field
    Ω : Set
    embed : ∀ {ℓ} → Tower.S Tow ℓ → HilbertSpace.H HS
    U : ℝ → HilbertSpace.H HS → HilbertSpace.H HS
    Hgen : Set
