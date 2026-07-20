module DASHI.Biology.BraidedEmotionEvidenceRegistry where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.BraidedEmotionTheoryContention as Contention

data EvidenceStatus : Set where
  replicatedAssociation : EvidenceStatus
  contestedAssociation : EvidenceStatus
  mechanisticCandidate : EvidenceStatus
  proxyOnly : EvidenceStatus
  theoryDependentInterpretation : EvidenceStatus
  phenomenologicalReport : EvidenceStatus
  culturalRelationalWarrant : EvidenceStatus
  normativeCommitment : EvidenceStatus

record EmotionEvidenceRow : Set where
  constructor mkEmotionEvidenceRow
  field
    claimLabel : String
    theory : Contention.EmotionTheory
    scale : Contention.ExplanationScale
    status : EvidenceStatus
    populationOrContext : String
    supportingObservation : String
    potentialFalsifier : String
    theoremAuthorityClaimed : Bool
    clinicalAuthorityClaimed : Bool

open EmotionEvidenceRow public

record EmotionEvidenceBoundary : Set where
  constructor mkEmotionEvidenceBoundary
  field
    rows : List EmotionEvidenceRow
    technicalVocabularyIsNotEvidence : Bool
    proxyIsNotMechanism : Bool
    associationIsNotCausation : Bool
    normativeCommitmentIsNotEmpiricalResult : Bool
    emptyRegistryDoesNotPromoteTheory : Bool
    boundaryHolds : Bool
    boundaryHoldsIsTrue : boundaryHolds ≡ true

open EmotionEvidenceBoundary public

canonicalEmotionEvidenceBoundary : EmotionEvidenceBoundary
canonicalEmotionEvidenceBoundary =
  mkEmotionEvidenceBoundary [] true true true true true true refl
