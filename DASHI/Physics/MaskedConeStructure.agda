module DASHI.Physics.MaskedConeStructure where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ; +_) renaming (_≤_ to _≤ᵢ_; _<_ to _<ᵢ_)
open import Data.Nat renaming (_≤_ to _≤ₙ_) hiding (_<_)
open import Data.Vec using (Vec)

open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ
open import DASHI.Physics.SignatureFromMask as SFM

------------------------------------------------------------------------
-- Cone predicates

Timelike : ∀ {m : Nat} → Vec IMQ.Sign m → Vec Trit m → Set
Timelike σ x = (+ 0) <ᵢ IMQ.Qσ σ x

Spacelike : ∀ {m : Nat} → Vec IMQ.Sign m → Vec Trit m → Set
Spacelike σ x = IMQ.Qσ σ x <ᵢ (+ 0)

Null : ∀ {m : Nat} → Vec IMQ.Sign m → Vec Trit m → Set
Null σ x = IMQ.Qσ σ x ≡ (+ 0)

------------------------------------------------------------------------
-- Causal structure seam (delta encodes the “difference” along the order)

record CausalStructure (m : Nat) : Set₁ where
  field
    _≼_  : Vec Trit m → Vec Trit m → Set
    delta : Vec Trit m → Vec Trit m → Vec Trit m

------------------------------------------------------------------------
-- Cone monotonicity seam (moved to MaskedConeStructureAssumptions)

------------------------------------------------------------------------
-- Unique time direction seam

TwoTimeLike : ∀ {m : Nat} → Vec IMQ.Sign m → Set
TwoTimeLike σ = (suc (suc 0)) ≤ₙ SFM.countMinus σ

record UniqueFixedPoint {A : Set} (T : A → A) : Set where
  field
    fp : A
    unique : ∀ x → T x ≡ x → x ≡ fp

¬_ : Set → Set
¬ P = P → ⊥

-- Unique fixed-point obstruction (moved to MaskedConeStructureAssumptions)
