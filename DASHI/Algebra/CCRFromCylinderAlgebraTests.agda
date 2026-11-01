module DASHI.Algebra.CCRFromCylinderAlgebraTests where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma

------------------------------------------------------------------------
-- Abstract Hilbert space + operators
------------------------------------------------------------------------

record CCRTestAxioms : Set₁ where
  field
    H : Set
    _≈_ : H → H → Set

    -- Bounded linear operators (kept abstract)
    Op : Set
    _∘_ : Op → Op → Op
    _Op+_ : Op → Op → Op
    _Op-_ : Op → Op → Op
    _Op*_ : Op → Op → Op

    I   : Op                    -- identity
    act : Op → H → H            -- operator action

    -- Cylinder / depth primitives (abstract)
    Depth : Set
    refine : Depth → Depth        -- refinement generator
    coarse : Depth → Depth        -- truncation / depth translation
    D-op R-op : Op                -- operators induced by coarse/refine

    -- Planck/phase grain parameter ħ (kept abstract)
    ħ : Set
    iħI : Op                      -- “i ħ I” as an operator placeholder

    -- Limit notion: strong operator limit along N→∞ with k/N fixed.
    Seq : Set
    limStrong : (Seq → Op) → Op → Set
    scaledCommutator : Seq → Op   -- (N,k) ↦ scaling * [D,R]

    -- CCR Theorem (test): scaled commutator → i ħ I in strong limit
    CCR-StrongLimit :
      limStrong scaledCommutator iħI

open CCRTestAxioms public

-- Commutator
_bracket_ : ∀ {A : CCRTestAxioms} → Op A → Op A → Op A
_bracket_ {A} op1 op2 =
  CCRTestAxioms._Op-_ A
    (CCRTestAxioms._∘_ A op1 op2)
    (CCRTestAxioms._∘_ A op2 op1)
