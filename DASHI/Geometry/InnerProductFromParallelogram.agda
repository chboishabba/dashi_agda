module DASHI.Geometry.InnerProductFromParallelogram where

open import Level using (Level; suc)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (⊤; tt)

open import DASHI.Geometry.Parallelogram
import DASHI.Geometry.ParallelogramToInnerProduct as PTI
open import DASHI.Core.Q using (ℚ)

record InnerProduct (ℓ : Level) : Set (suc ℓ) where
  field
    V : Set ℓ
    ⟪_,_⟫ : V → V → ℚ

toInnerProduct :
  ∀ {ℓ} → PTI.InnerProduct ℓ → InnerProduct ℓ
toInnerProduct ip =
  record
    { V = PTI.InnerProduct.V ip
    ; ⟪_,_⟫ = PTI.InnerProduct.⟪_,_⟫ ip
    }

Parallelogram⇒InnerProduct :
  ∀ {ℓ} (N : NormedSpace ℓ) →
  Parallelogram N →
  Σ (InnerProduct ℓ) (λ _ → ⊤)
Parallelogram⇒InnerProduct N para =
  toInnerProduct (PTI.Parallelogram⇒InnerProduct N para) , tt
