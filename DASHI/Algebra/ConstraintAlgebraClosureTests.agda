module DASHI.Algebra.ConstraintAlgebraClosureTests where

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

------------------------------------------------------------------------
-- Abstract operator Lie algebra (commutator bracket)
------------------------------------------------------------------------

record ConstraintAlgebraStructure : Set₁ where
  field
    Op : Set
    _∘_ : Op → Op → Op
    _-_ : Op → Op → Op
    I   : Op

    -- Constraints: Hamiltonian + Momentum (vector-index abstracted)
    Idx : Set
    H    : Op
    Hᵢ   : Idx → Op

open ConstraintAlgebraStructure public

_bracket_ : (S : ConstraintAlgebraStructure) → Op S → Op S → Op S
_bracket_ S X Y = (_-_ S) ((_∘_ S) X Y) ((_∘_ S) Y X)

------------------------------------------------------------------------
-- Closure statement: commutators of constraints re-express as constraints
------------------------------------------------------------------------

record DiracClosure (S : ConstraintAlgebraStructure) : Set where
  field
    -- [Hᵢ, Hⱼ] = H_k(...)
    mom-mom :
      ∀ i j → Σ (Idx S) (λ k → (_bracket_ S (Hᵢ S i) (Hᵢ S j)) ≡ Hᵢ S k)

    -- [H, Hᵢ] = H(...)
    ham-mom :
      ∀ i → (_bracket_ S (H S) (Hᵢ S i)) ≡ H S

    -- [H, H] = Hᵢ(...)
    ham-ham :
      Σ (Idx S) (λ k → (_bracket_ S (H S) (H S)) ≡ Hᵢ S k)

------------------------------------------------------------------------
-- Axiom bundle (no postulates)
------------------------------------------------------------------------

record ConstraintAlgebraAxioms : Set₁ where
  field
    struct : ConstraintAlgebraStructure
    ValuationEquivariance : Set     -- “decimation commutes with relabellings”
    NoLeakageStability    : Set     -- fixed-point stability condition
    closure : DiracClosure struct

open ConstraintAlgebraAxioms public

ConstraintAlgebraTheorem :
  (A : ConstraintAlgebraAxioms) →
  DiracClosure (struct A)
ConstraintAlgebraTheorem A = closure A
