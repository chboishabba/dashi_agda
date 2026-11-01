module DASHI.Cognition.PNF.SensibLawCullenEdelman64SemanticStateCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence
import DASHI.Cognition.PNF.SensibLawAttributedSourcePNFCandidateWeldExact as CandidateWeld
import DASHI.Cognition.PNF.SensibLawCullenEdelman64WrongTypeSourceRealisationExact as Source64

------------------------------------------------------------------------
-- CULLEN / EDELMAN [64] SEMANTIC-STATE COMPILER
--
-- This does not fabricate a parser candidate.  It compiles a legal semantic
-- state only after an AttributedPNFCandidateWeld proves that the candidate fibre
-- belongs to the canonical Cullen primary source and exact [64] source span.
------------------------------------------------------------------------

edelman64Event : Ontology.Event
edelman64Event = Ontology.event
  (Ontology.stableId "event:Cullen:OSG-intervention")
  (Ontology.stableId "event-class:police-crowd-control-intervention")
  "Cullen source chronology / exact event time not fixed by this compiler"
  "OSG intervention discussed in Cullen v New South Wales [2026] HCA 19"

edelman64Perspective : Ontology.Perspective
edelman64Perspective = Ontology.perspectiveRecord
  (Ontology.stableId "perspective:Cullen:Edelman-J")
  (Ontology.stableId "actor:judicial:Edelman-J")
  "Edelman J reasons"

edelman64WrongTypeInterpretation : Ontology.WrongTypeInterpretation
edelman64WrongTypeInterpretation = Ontology.interpretation
  (Ontology.Event.eventId edelman64Event)
  (Ontology.WrongType.wrongTypeId Negligence.negligenceWrongType)
  Negligence.auCommonLawSystem
  (Ontology.Perspective.perspectiveId edelman64Perspective)
  Ontology.suggested
  []
  "source-reviewed Cullen [64] candidate classification; applicability remains separately payable"

record Edelman64AttributedCandidate : Set₁ where
  constructor edelman64-attributed-candidate
  field
    weld : CandidateWeld.AttributedPNFCandidateWeld
    sourceIsCanonicalCullen :
      CandidateWeld.attributedSource weld ≡ Source64.edelman64PrimarySource
    locatorIsEdelman64 :
      CandidateWeld.sourceLocator weld ≡ Source64.edelman64Locator

open Edelman64AttributedCandidate public

edelman64EventStatus : Status.EventStatusProduct
edelman64EventStatus = Status.eventStatusProduct
  (Ontology.StableId.value (Ontology.Event.eventId edelman64Event))
  Status.assertedOccurrence
  Status.eventTime
  Status.scopeResolved

edelman64DutyPropositionStatus : Status.PropositionStatusProduct
edelman64DutyPropositionStatus = Status.propositionStatusProduct
  (Ontology.StableId.value
    (Algebra.propositionId Source64.edelman64OrdinaryCommonLawDuty))
  Status.assertedBySource
  Status.truthUnresolved
  Status.propositionSource
  Status.evidenceFor
  Status.sourceEvidence
  Status.modalityKindUnresolved
  Status.modalForceUnresolved
  Status.scopeResolved

edelman64LegalStatus : Status.LegalStatusProduct
edelman64LegalStatus = Status.legalStatusProduct
  Status.courtJurisdiction
  Status.legalAuthority
  Status.conditionUnresolved
  Status.applicabilityCandidate
  Status.violationUnresolved
  Status.liabilityUnresolved
  Status.burdenKindUnresolved
  Status.standardUnresolved
  Status.ratioCandidate
  Status.duty

record Edelman64StateInput : Set₁ where
  constructor edelman64-state-input
  field
    attributedCandidate : Edelman64AttributedCandidate
    subjects : List Status.SemanticSubject

open Edelman64StateInput public

compileEdelman64State : Edelman64StateInput → Status.SemanticCommitmentState
compileEdelman64State input = Status.semanticCommitmentState
  (CandidateWeld.candidateFibre (weld (attributedCandidate input)))
  (subjects input)
  (edelman64EventStatus ∷ [])
  (edelman64DutyPropositionStatus ∷ [])
  (edelman64LegalStatus ∷ [])
  true
  false

compiledStateUsesExactAttributedCandidate :
  (input : Edelman64StateInput) →
  Status.sourceCandidate (compileEdelman64State input)
  ≡ CandidateWeld.candidateFibre (weld (attributedCandidate input))
compiledStateUsesExactAttributedCandidate input = refl

compiledStateRemainsCandidateOnly :
  (input : Edelman64StateInput) →
  Status.candidateOnly (compileEdelman64State input) ≡ true
compiledStateRemainsCandidateOnly input = refl

compiledStateHasNoGovernedAdmissionByConstruction :
  (input : Edelman64StateInput) →
  Status.governedAdmissionPresent (compileEdelman64State input) ≡ false
compiledStateHasNoGovernedAdmissionByConstruction input = refl

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data SourceWeldAutomaticallyAdmitsApplicability : Set where
data SourceWeldAutomaticallyProvesOccurrence : Set where
data RatioCandidateAutomaticallyMeansBindingRatio : Set where
data CandidateStateAutomaticallyCreatesViolation : Set where
data CandidateStateAutomaticallyCreatesLiability : Set where

sourceWeldDoesNotAdmitApplicability :
  SourceWeldAutomaticallyAdmitsApplicability → ⊥
sourceWeldDoesNotAdmitApplicability ()

sourceWeldDoesNotProveOccurrence :
  SourceWeldAutomaticallyProvesOccurrence → ⊥
sourceWeldDoesNotProveOccurrence ()

ratioCandidateDoesNotBecomeBindingRatio :
  RatioCandidateAutomaticallyMeansBindingRatio → ⊥
ratioCandidateDoesNotBecomeBindingRatio ()

candidateStateDoesNotCreateViolation :
  CandidateStateAutomaticallyCreatesViolation → ⊥
candidateStateDoesNotCreateViolation ()

candidateStateDoesNotCreateLiability :
  CandidateStateAutomaticallyCreatesLiability → ⊥
candidateStateDoesNotCreateLiability ()

stateCompilerReading : String
stateCompilerReading =
  "The Cullen [64] SemanticCommitmentState is compilable only from a review-welded AttributedSource + PNF source span + SemanticCandidateFibre. The resulting state remains candidate-only: WrongType, duty element, applicability, violation and liability still require their independent receipts."
