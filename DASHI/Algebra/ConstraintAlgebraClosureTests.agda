{-# OPTIONS --allow-unsolved-metas #-}
module DASHI.Algebra.ConstraintAlgebraClosureTests where

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

------------------------------------------------------------------------
-- Abstract operator Lie algebra (commutator bracket)
------------------------------------------------------------------------

postulate
  Op : Set
  _∘_ : Op → Op → Op
  _-_ : Op → Op → Op
  I   : Op

infixl 9 _∘_

_bracket_ : Op → Op → Op
A bracket B = (A ∘ B) - (B ∘ A)

------------------------------------------------------------------------
-- Constraints: Hamiltonian + Momentum (vector-index abstracted)
------------------------------------------------------------------------

postulate
  Idx : Set
  H    : Op
  Hᵢ   : Idx → Op

------------------------------------------------------------------------
-- Closure statement: commutators of constraints re-express as constraints
-- (This is the “no anomaly” test: algebra closes in the same family.)
------------------------------------------------------------------------

record DiracClosure : Set where
  field
    -- [Hᵢ, Hⱼ] = H_k(...)   (structure functions hidden for now)
    mom-mom :
      ∀ i j → Σ Idx (λ k → (Hᵢ i bracket Hᵢ j) ≡ Hᵢ k)

    -- [H, Hᵢ] = H(...)
    ham-mom :
      ∀ i → (H bracket Hᵢ i) ≡ H

    -- [H, H] = Hᵢ(...)
    ham-ham :
      Σ Idx (λ k → (H bracket H) ≡ Hᵢ k)

------------------------------------------------------------------------
-- Theorem obligation: derive closure from “valuation equivariance”
------------------------------------------------------------------------

postulate
  ValuationEquivariance : Set     -- your “decimation commutes with relabellings”
  NoLeakageStability    : Set     -- your fixed-point stability condition

postulate
  ConstraintAlgebraTheorem :
    ValuationEquivariance →
    NoLeakageStability →
    DiracClosure
