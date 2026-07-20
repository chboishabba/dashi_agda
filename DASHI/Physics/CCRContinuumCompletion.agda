module DASHI.Physics.CCRContinuumCompletion where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.CCRAssumptions as CCR

record Convergence {A : Set} : Set₁ where
  field
    _⟶_ : (Nat → A) → A → Set

record CCRApproximation
  (A : CCR.OperatorAlgebra)
  (C : Convergence {A = CCR.OperatorAlgebra.Op A}) : Set₁ where
  open CCR.OperatorAlgebra A
  open Convergence C
  field
    Dₙ Rₙ : Nat → Op
    ħ : Scalar
    commutatorSequence : Nat → Op
    commutatorSequence-def : ∀ n →
      commutatorSequence n ≡ [ Dₙ n , Rₙ n ]
    convergesToCCR : commutatorSequence ⟶ s∙ ħ

record CCRContinuumClosure : Set₁ where
  field
    algebra : CCR.OperatorAlgebra
    convergence : Convergence {A = CCR.OperatorAlgebra.Op algebra}
    approximation : CCRApproximation algebra convergence

open CCRContinuumClosure public
