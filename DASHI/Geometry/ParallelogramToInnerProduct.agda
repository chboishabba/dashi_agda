
module DASHI.Geometry.ParallelogramToInnerProduct where

open import Level using (Level; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Unit using (⊤; tt)

open import DASHI.Geometry.Parallelogram
open import DASHI.Core.Q as Q using (ℚ; _+ℚ_; _-ℚ_; _*ℚ_; fourℚ)
open import Data.Integer using (+_)
open import Agda.Builtin.Nat using (Nat)

record InnerProduct (ℓ : Level) : Set (suc ℓ) where
  field
    V : Set ℓ
    ⟪_,_⟫ : V → V → ℚ

-- Polarization formula (no further properties required here).
polarization :
  ∀ {ℓ} (N : NormedSpace ℓ) →
  NormedSpace.V N → NormedSpace.V N → ℚ
polarization N x y =
  let open NormedSpace N in
  let inv4 : ℚ
      inv4 = Q._/_ (+ 1) 4
      num : ℚ
      num = ((‖ (x + y) ‖ *ℚ ‖ (x + y) ‖) -ℚ (‖ (x - y) ‖ *ℚ ‖ (x - y) ‖))
  in inv4 *ℚ num

Parallelogram⇒InnerProduct :
  ∀ {ℓ} (N : NormedSpace ℓ) →
  Parallelogram N →
  InnerProduct ℓ
Parallelogram⇒InnerProduct N _ =
  record
    { V = NormedSpace.V N
    ; ⟪_,_⟫ = polarization N
    }
