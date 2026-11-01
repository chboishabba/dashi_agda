module DASHI.Geometry.Signature31AndDim3 where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)

-- All data/axioms are parameters; no vacuous defaults.

record LorentzData : Set₁ where
  field
    QuadraticForm : Set
    Signature : Set
    sig31 : Signature
    sig : QuadraticForm → Signature
    Cone : Set
    coneOf : QuadraticForm → Cone

record CausalAxioms (D : LorentzData) : Set₁ where
  field
    isotropy : ∀ (Q : LorentzData.QuadraticForm D) → Set
    finiteSpeed : ∀ (Q : LorentzData.QuadraticForm D) → Set
    convex : ∀ (Q : LorentzData.QuadraticForm D) → Set
    nondeg : ∀ (Q : LorentzData.QuadraticForm D) → Set
    cone-determines-Q :
      ∀ (Q Q' : LorentzData.QuadraticForm D) →
      LorentzData.coneOf D Q ≡ LorentzData.coneOf D Q' →
      LorentzData.sig D Q ≡ LorentzData.sig D Q'

open CausalAxioms public

SignatureUniqueness :
  ∀ {D} → CausalAxioms D → Set
SignatureUniqueness {D} A =
  ∀ (Q : LorentzData.QuadraticForm D) →
  isotropy A Q →
  finiteSpeed A Q →
  convex A Q →
  nondeg A Q →
  LorentzData.sig D Q ≡ LorentzData.sig31 D

record Dim3Witness (D : LorentzData) : Set₁ where
  field dim3 : Set

record LorentzDimClosure {D} (A : CausalAxioms D) : Set₁ where
  field
    sigProof : SignatureUniqueness A
    dimProof : Dim3Witness D

mkLorentzDimClosure :
  ∀ {D} (A : CausalAxioms D) →
  SignatureUniqueness A →
  Dim3Witness D →
  LorentzDimClosure A
mkLorentzDimClosure A sigPf dimPf =
  record { sigProof = sigPf ; dimProof = dimPf }
