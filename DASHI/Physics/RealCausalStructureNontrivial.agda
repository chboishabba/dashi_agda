module DASHI.Physics.RealCausalStructureNontrivial where

open import Agda.Builtin.Nat using (Nat)
open import Data.Integer using (ℤ; +_) renaming (_≤_ to _≤ᵢ_)
open import Data.Vec using (Vec)

open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ
open import DASHI.Physics.MaskedConeStructure as MCS

------------------------------------------------------------------------
-- Nontrivial causal structure: order requires Qσ(x) ≥ 0, delta = x

maskCausal : ∀ {m : Nat} (σ : Vec IMQ.Sign m) → MCS.CausalStructure m
maskCausal {m} σ =
  record
    { _≼_ = λ x _ → (+ 0) ≤ᵢ IMQ.Qσ σ x
    ; delta = λ x _ → x
    }

coneMonotone-mask :
  ∀ {m : Nat} (σ : Vec IMQ.Sign m) (x y : Vec Trit m) →
  MCS.CausalStructure._≼_ (maskCausal σ) x y →
  (+ 0) ≤ᵢ IMQ.Qσ σ (MCS.CausalStructure.delta (maskCausal σ) x y)
coneMonotone-mask σ x y h = h
