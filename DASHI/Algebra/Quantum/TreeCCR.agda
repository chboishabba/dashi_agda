module DASHI.Algebra.Quantum.TreeCCR where

open import Data.Nat

record TreeCCRAxioms : Set₁ where
  field
    ℝ : Set
    TreeDepth : ℕ → Set
    LeafNodes : ℕ → ℕ
    InducedH : ℕ → Set
    RefinementMap : ∀ n → InducedH n → InducedH (suc n)

open TreeCCRAxioms public
