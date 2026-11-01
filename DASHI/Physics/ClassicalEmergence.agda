module DASHI.Physics.ClassicalEmergence where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat using (_≤_)

open import DASHI.Physics.PhysicalTheory as PT

record QuantumEvolution (ℓ : Level) : Set (lsuc ℓ) where
  field
    QState : Set ℓ
    evolve : QState → QState

record ClassicalEmergence {ℓ : Level}
  (QEv : QuantumEvolution ℓ)
  (Cl : PT.PhysicalTheory ℓ) : Set (lsuc ℓ) where
  open QuantumEvolution QEv
  field
    coarse : QState → PT.State Cl

    coarse-inv : ∀ q → PT.Inv Cl (coarse q)
    commute≈   : ∀ q → coarse (evolve q) ≡ PT.step Cl (coarse q)

record ApproxClassicalEmergence {ℓ : Level}
  (QEv : QuantumEvolution ℓ)
  (Cl : PT.PhysicalTheory ℓ) : Set (lsuc ℓ) where
  open QuantumEvolution QEv
  field
    coarse : QState → PT.State Cl
    _≈cl_  : PT.State Cl → PT.State Cl → Set ℓ

    coarse-inv : ∀ q → PT.Inv Cl (coarse q)
    commute≈   : ∀ q → coarse (evolve q) ≈cl PT.step Cl (coarse q)

record ContractiveEmergence {ℓ : Level}
  (QEv : QuantumEvolution ℓ)
  (Cl : PT.PhysicalTheory ℓ) : Set (lsuc ℓ) where
  field
    emergence : ApproxClassicalEmergence QEv Cl

    effective-defect-descent :
      ∀ q →
      PT.defectSize Cl
        (ApproxClassicalEmergence.coarse emergence (QuantumEvolution.evolve QEv q))
      ≤
      PT.defectSize Cl
        (ApproxClassicalEmergence.coarse emergence q)
