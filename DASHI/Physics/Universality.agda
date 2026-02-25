module DASHI.Physics.Universality where

open import Level using (Level; suc; _⊔_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_)

record PhysicsClosureClaims (ℓ : Level) : Set (suc ℓ) where
  field
    Carrier : Set ℓ
    MetricEmergence  : ⊤
    Signature31      : ⊤
    ConstraintClosure : ⊤
    MDLLyapunov      : ⊤

open PhysicsClosureClaims public

record Instance (ℓ : Level) : Set (suc ℓ) where
  field
    Claims : PhysicsClosureClaims ℓ

open Instance public

postulate
  HEPInstance     : ∀ {ℓ} → Instance ℓ
  PrimesInstance  : ∀ {ℓ} → Instance ℓ
  SignalsInstance : ∀ {ℓ} → Instance ℓ

postulate
  UniversalityTheorem :
    ∀ {ℓ} (I : Instance ℓ) → ⊤
