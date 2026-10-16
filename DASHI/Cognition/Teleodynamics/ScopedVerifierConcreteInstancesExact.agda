module DASHI.Cognition.Teleodynamics.ScopedVerifierConcreteInstancesExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)

import DASHI.Cognition.Teleodynamics.ScopedVerifierArchitectureExact as Verify

-- Two deliberately small exact validators: one validates shape/syntax admission,
-- the other validates provenance admission.  Their conjunction illustrates the
-- intended architecture without pretending either is a semantic truth oracle.

record CandidateArtifact : Set where
  constructor candidate-artifact
  field
    syntaxOK : Bool
    provenanceOK : Bool
open CandidateArtifact public

boolStatus : Bool → Verify.VerificationStatus
boolStatus true = Verify.verified
boolStatus false = Verify.refuted

syntaxValidator : Verify.ScopedValidator CandidateArtifact
syntaxValidator = Verify.scoped-validator
  (λ _ → ⊤)
  (λ x → syntaxOK x ≡ true)
  (λ x → syntaxOK x ≡ true)
  (λ x → boolStatus (syntaxOK x))
  accept
  sound
  where
  accept : (x : CandidateArtifact) → boolStatus (syntaxOK x) ≡ Verify.verified → syntaxOK x ≡ true
  accept (candidate-artifact true p) eq = refl
  accept (candidate-artifact false p) ()

  sound : (x : CandidateArtifact) → ⊤ → boolStatus (syntaxOK x) ≡ Verify.verified → syntaxOK x ≡ true
  sound x tt eq = accept x eq

provenanceValidator : Verify.ScopedValidator CandidateArtifact
provenanceValidator = Verify.scoped-validator
  (λ _ → ⊤)
  (λ x → provenanceOK x ≡ true)
  (λ x → provenanceOK x ≡ true)
  (λ x → boolStatus (provenanceOK x))
  accept
  sound
  where
  accept : (x : CandidateArtifact) → boolStatus (provenanceOK x) ≡ Verify.verified → provenanceOK x ≡ true
  accept (candidate-artifact s true) eq = refl
  accept (candidate-artifact s false) ()

  sound : (x : CandidateArtifact) → ⊤ → boolStatus (provenanceOK x) ≡ Verify.verified → provenanceOK x ≡ true
  sound x tt eq = accept x eq

fullyAdmitted : CandidateArtifact
fullyAdmitted = candidate-artifact true true

syntaxReceipt : Verify.ValidationReceipt syntaxValidator fullyAdmitted
syntaxReceipt = Verify.receiptFromVerified syntaxValidator fullyAdmitted tt refl

provenanceReceipt : Verify.ValidationReceipt provenanceValidator fullyAdmitted
provenanceReceipt = Verify.receiptFromVerified provenanceValidator fullyAdmitted tt refl

composedReceipt : Verify.PairValidationReceipt syntaxValidator provenanceValidator fullyAdmitted
composedReceipt = Verify.pair-validation-receipt syntaxReceipt provenanceReceipt

bothClaimsPaid : syntaxOK fullyAdmitted ≡ true × provenanceOK fullyAdmitted ≡ true
bothClaimsPaid = Verify.pairClaimsPaid composedReceipt
