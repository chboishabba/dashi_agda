module DASHI.Physics.Universality where

open import Level using (Level; suc; _⊔_; Lift)
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

open import Agda.Primitive using (Setω)

record UniversalityAxioms : Setω where
  field
    HEPInstance     : ∀ {ℓ} → Instance ℓ
    PrimesInstance  : ∀ {ℓ} → Instance ℓ
    SignalsInstance : ∀ {ℓ} → Instance ℓ

    UniversalityTheorem :
      ∀ {ℓ} (I : Instance ℓ) → ⊤

HEPInstance : UniversalityAxioms → ∀ {ℓ} → Instance ℓ
HEPInstance A = UniversalityAxioms.HEPInstance A

PrimesInstance : UniversalityAxioms → ∀ {ℓ} → Instance ℓ
PrimesInstance A = UniversalityAxioms.PrimesInstance A

SignalsInstance : UniversalityAxioms → ∀ {ℓ} → Instance ℓ
SignalsInstance A = UniversalityAxioms.SignalsInstance A

UniversalityTheorem : (A : UniversalityAxioms) → ∀ {ℓ} (I : Instance ℓ) → ⊤
UniversalityTheorem A = UniversalityAxioms.UniversalityTheorem A

universalityAxiomsDefault : UniversalityAxioms
universalityAxiomsDefault =
  record
    { HEPInstance = λ {ℓ} → record { Claims = record
        { Carrier = Lift ℓ ⊤
        ; MetricEmergence = tt
        ; Signature31 = tt
        ; ConstraintClosure = tt
        ; MDLLyapunov = tt
        } }
    ; PrimesInstance = λ {ℓ} → record { Claims = record
        { Carrier = Lift ℓ ⊤
        ; MetricEmergence = tt
        ; Signature31 = tt
        ; ConstraintClosure = tt
        ; MDLLyapunov = tt
        } }
    ; SignalsInstance = λ {ℓ} → record { Claims = record
        { Carrier = Lift ℓ ⊤
        ; MetricEmergence = tt
        ; Signature31 = tt
        ; ConstraintClosure = tt
        ; MDLLyapunov = tt
        } }
    ; UniversalityTheorem = λ {ℓ} _ → tt
    }
