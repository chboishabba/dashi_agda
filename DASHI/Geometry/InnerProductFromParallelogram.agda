module DASHI.Geometry.InnerProductFromParallelogram where

open import Level using (Level; suc)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (⊤)

open import DASHI.Geometry.Parallelogram
open import DASHI.Geometry.Polarization
open import DASHI.Core.Q using (ℚ)

record InnerProduct (ℓ : Level) : Set (suc ℓ) where
  field
    V : Set ℓ
    ⟪_,_⟫ : V → V → ℚ

postulate
  Parallelogram⇒InnerProduct :
    ∀ {ℓ} (N : NormedSpace ℓ) →
    Parallelogram N →
    Σ (InnerProduct ℓ) (λ _ → ⊤)
