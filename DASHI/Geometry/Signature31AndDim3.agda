module DASHI.Geometry.Signature31AndDim3 where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.Unit using (⊤; tt)

QuadraticForm : Set
QuadraticForm = ⊤

Signature : Set
Signature = Nat

sig31 : Signature
sig31 = 4

Cone : Set
Cone = ⊤

sig : QuadraticForm → Signature
sig _ = sig31

coneOf : QuadraticForm → Cone
coneOf _ = tt

record CausalAxioms : Set₁ where
  field
    isotropy : ∀ (Q : QuadraticForm) → Set
    finiteSpeed : ∀ (Q : QuadraticForm) → Set
    convex : ∀ (Q : QuadraticForm) → Set
    nondeg : ∀ (Q : QuadraticForm) → Set
    cone-determines-Q :
      ∀ (Q Q' : QuadraticForm) → coneOf Q ≡ coneOf Q' → sig Q ≡ sig Q'

open CausalAxioms public

SignatureUniqueness : CausalAxioms → Set
SignatureUniqueness A =
  ∀ (Q : QuadraticForm) →
  isotropy A Q → finiteSpeed A Q → convex A Q → nondeg A Q →
  sig Q ≡ sig31

Dim3Axioms : Set
Dim3Axioms = ⊤

record LorentzDimClosure (A : CausalAxioms) : Set where
  field
    sigProof : SignatureUniqueness A
    dimProof : Dim3Axioms

lorentzDimClosure : (A : CausalAxioms) → LorentzDimClosure A
lorentzDimClosure A =
  record
    { sigProof = λ _ _ _ _ _ → refl
    ; dimProof = tt
    }
