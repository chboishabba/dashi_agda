module DASHI.Algebra.Quantum.QutritUnitaryBridge where

open import DASHI.Core.OperatorTypes using (Invertible)
open import DASHI.Algebra.Quantum.Unitary
open import DASHI.Algebra.Quantum.TernaryCircuit

------------------------------------------------------------------------
-- The basis permutation is already constructively invertible.  To promote it
-- to the repo's quantum `Unitary` interface one supplies only the selected
-- inner product and its preservation theorem.

cycleQutritInvertible : Invertible cycleQutrit
cycleQutritInvertible =
  record
    { inv = inverseCycleQutrit
    ; left = inverseCycleLeft
    ; right = inverseCycleRight
    }

inverseCycleQutritInvertible : Invertible inverseCycleQutrit
inverseCycleQutritInvertible =
  record
    { inv = cycleQutrit
    ; left = inverseCycleRight
    ; right = inverseCycleLeft
    }

record QutritInnerProductAuthority (A : ComplexAxioms) : Set₁ where
  field
    qutritInnerProductSpace : InnerProductSpace A QutritBasis

    cyclePreservesInnerProduct :
      ∀ x y →
      ComplexAxioms._≡ℂ_ A
        (InnerProductSpace.⟪_,_⟫
          qutritInnerProductSpace
          (cycleQutrit x)
          (cycleQutrit y))
        (InnerProductSpace.⟪_,_⟫ qutritInnerProductSpace x y)

    inverseCyclePreservesInnerProduct :
      ∀ x y →
      ComplexAxioms._≡ℂ_ A
        (InnerProductSpace.⟪_,_⟫
          qutritInnerProductSpace
          (inverseCycleQutrit x)
          (inverseCycleQutrit y))
        (InnerProductSpace.⟪_,_⟫ qutritInnerProductSpace x y)

open QutritInnerProductAuthority public

cycleQutritUnitary :
  ∀ {A : ComplexAxioms} →
  (Q : QutritInnerProductAuthority A) →
  Unitary (qutritInnerProductSpace Q) cycleQutrit
cycleQutritUnitary Q =
  record
    { inv = cycleQutritInvertible
    ; preserves = cyclePreservesInnerProduct Q
    }

inverseCycleQutritUnitary :
  ∀ {A : ComplexAxioms} →
  (Q : QutritInnerProductAuthority A) →
  Unitary (qutritInnerProductSpace Q) inverseCycleQutrit
inverseCycleQutritUnitary Q =
  record
    { inv = inverseCycleQutritInvertible
    ; preserves = inverseCyclePreservesInnerProduct Q
    }
