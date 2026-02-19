module DASHI.Algebra.Quantum.TreeCCR where

open import Data.Nat

postulate ℝ : Set

postulate
  TreeDepth : ℕ -> Set
  LeafNodes : ℕ -> ℕ
  InducedH : ℕ -> Set

postulate
  RefinementMap :
    ∀ n → InducedH n → InducedH (suc n)
