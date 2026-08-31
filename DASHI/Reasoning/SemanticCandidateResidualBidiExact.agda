module DASHI.Reasoning.SemanticCandidateResidualBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Core.CostedResidualInformationChoiceExact as Costed
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate

------------------------------------------------------------------------
-- CANDIDATE SEMANTIC AMBIGUITY AS A GENERIC BIDI RESIDUAL FIBRE
------------------------------------------------------------------------

infix 4 _∈_
data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

semanticCandidateFibre :
  Candidate.CandidateSemanticFibre →
  Bidi.ResidualFibre Candidate.CandidateSemanticFragment
semanticCandidateFibre fibre candidate =
  candidate ∈ Candidate.candidates fibre

------------------------------------------------------------------------
-- A new semantic/world/source constraint intersects the live candidate fibre.
-- This is the same generic information geometry used for experiments: more
-- warranted information may shrink ambiguity without forcing point resolution.
------------------------------------------------------------------------

SemanticConstraint : Set₁
SemanticConstraint = Candidate.CandidateSemanticFragment → Set

constrainedSemanticFibre :
  Candidate.CandidateSemanticFibre →
  SemanticConstraint →
  Bidi.ResidualFibre Candidate.CandidateSemanticFragment
constrainedSemanticFibre fibre constraint candidate =
  semanticCandidateFibre fibre candidate × constraint candidate

semanticConstraintAlwaysRefinesCandidateFibre :
  (fibre : Candidate.CandidateSemanticFibre) →
  (constraint : SemanticConstraint) →
  Bidi.FibreRefines
    (constrainedSemanticFibre fibre constraint)
    (semanticCandidateFibre fibre)
semanticConstraintAlwaysRefinesCandidateFibre fibre constraint candidate witness =
  proj₁ witness

record SemanticConstraintReceipt
    (fibre : Candidate.CandidateSemanticFibre)
    (constraint : SemanticConstraint) : Set₁ where
  constructor semanticConstraintReceipt
  field
    constraintSourceReference : String
    sourceOrWorldAuthorityReference : String
    scopeReference : String
    alternativesStillOpenReference : String
    validationReference : String

open SemanticConstraintReceipt public

------------------------------------------------------------------------
-- The older semantic-resolution record retained selected-in-fibre as a String
-- reference. This companion upgrades that one coordinate to an actual proof.
------------------------------------------------------------------------

record ProofRelevantSemanticResolution
    (fibre : Candidate.CandidateSemanticFibre) : Set₁ where
  constructor proofRelevantSemanticResolution
  field
    legacyResolution : Candidate.SemanticResolutionReceipt fibre
    selectedReallyInFibre :
      Candidate.selected legacyResolution ∈ Candidate.candidates fibre
    retainedAlternativeReference : String
    resolutionAuthorityReference : String

open ProofRelevantSemanticResolution public

------------------------------------------------------------------------
-- Semantic-resolution moves can now enter the generic costed information
-- selector, but only after an application supplies cost and certified gain.
------------------------------------------------------------------------

record SemanticResidualInformationMove
    (fibre : Candidate.CandidateSemanticFibre) : Set₁ where
  constructor semanticResidualInformationMove
  field
    constraint : SemanticConstraint
    constraintReceipt : SemanticConstraintReceipt fibre constraint
    cost : Nat
    certifiedGain : Nat
    gainCalibrationReference : String
    moveReference : String

open SemanticResidualInformationMove public

asCostedResidualMove :
  (fibre : Candidate.CandidateSemanticFibre) →
  SemanticResidualInformationMove fibre →
  Costed.ResidualInformationMove Candidate.CandidateSemanticFragment
asCostedResidualMove fibre move = Costed.residualInformationMove
  (semanticCandidateFibre fibre)
  (constrainedSemanticFibre fibre (constraint move))
  (semanticConstraintAlwaysRefinesCandidateFibre fibre (constraint move))
  Costed.contextAuditResidualMove
  (cost move)
  (certifiedGain move)
  (moveReference move)
  (gainCalibrationReference move)
  (SemanticConstraintReceipt.sourceOrWorldAuthorityReference (constraintReceipt move))
  (SemanticConstraintReceipt.scopeReference (constraintReceipt move))
  (SemanticConstraintReceipt.alternativesStillOpenReference (constraintReceipt move))

record SemanticResidualBoundary : Set where
  constructor semanticResidualBoundary
  field
    ambiguityIsGenericResidualInformation : Bool
    ambiguityIsGenericResidualInformationIsTrue :
      ambiguityIsGenericResidualInformation ≡ true
    sourceWorldResolutionMayShrinkSemanticFibre : Bool
    sourceWorldResolutionMayShrinkSemanticFibreIsTrue :
      sourceWorldResolutionMayShrinkSemanticFibre ≡ true
    shrinkingSemanticFibreMeansWorldTruth : Bool
    shrinkingSemanticFibreMeansWorldTruthIsFalse :
      shrinkingSemanticFibreMeansWorldTruth ≡ false
    selectedCandidateMembershipCanBeProofRelevant : Bool
    selectedCandidateMembershipCanBeProofRelevantIsTrue :
      selectedCandidateMembershipCanBeProofRelevant ≡ true
    semanticResolutionMoveNeedsGainCalibration : Bool
    semanticResolutionMoveNeedsGainCalibrationIsTrue :
      semanticResolutionMoveNeedsGainCalibration ≡ true

canonicalSemanticResidualBoundary : SemanticResidualBoundary
canonicalSemanticResidualBoundary =
  semanticResidualBoundary true refl true refl false refl true refl true refl
