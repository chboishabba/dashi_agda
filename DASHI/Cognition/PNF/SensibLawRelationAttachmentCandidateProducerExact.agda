module DASHI.Cognition.PNF.SensibLawRelationAttachmentCandidateProducerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.ContextualFractranDirectDeltaAdapterExact as Contextual
import DASHI.Cognition.PNF.SensibLawLegalSemanticAdmissionFrontierExact as Admission

------------------------------------------------------------------------
-- Structural relation syntax is a candidate producer, not legal semantics.
--
-- The measured v0.4 relation/attachment queue contains seven spaCy dependency
-- surfaces.  The runtime producer may preserve these as exact candidate kinds
-- while deferring the legal-semantic interpretation to a later contextual
-- resolution/admission receipt.
------------------------------------------------------------------------

data RelationAttachmentKind : Set where
  preposition : RelationAttachmentKind
  prepositionalObject : RelationAttachmentKind
  prepositionalComplement : RelationAttachmentKind
  passiveAgentMarker : RelationAttachmentKind
  dative : RelationAttachmentKind
  caseMarker : RelationAttachmentKind
  particle : RelationAttachmentKind

record RelationAttachmentCandidate : Set where
  constructor relationAttachmentCandidate
  field
    kind : RelationAttachmentKind
    sentenceId : Nat
    localOrdinal : Nat
    candidateOnly : Bool
    contextResolutionRequired : Bool

open RelationAttachmentCandidate public

record RelationProducerReceipt : Set where
  constructor relationProducerReceipt
  field
    candidate : RelationAttachmentCandidate
    directReferenceParity : Bool
    canonicalExpandedObservationUnchanged : Bool
    semanticAuthorityGranted : Bool
    publicationEffect : Bool

open RelationProducerReceipt public

canonicalRelationProducerBoundary : RelationProducerReceipt
canonicalRelationProducerBoundary =
  relationProducerReceipt
    (relationAttachmentCandidate preposition 0 0 true true)
    true
    true
    false
    false

candidateOnlyIsTrue :
  candidateOnly (candidate canonicalRelationProducerBoundary) ≡ true
candidateOnlyIsTrue = refl

contextResolutionRequiredIsTrue :
  contextResolutionRequired (candidate canonicalRelationProducerBoundary) ≡ true
contextResolutionRequiredIsTrue = refl

semanticAuthorityGrantedIsFalse :
  semanticAuthorityGranted canonicalRelationProducerBoundary ≡ false
semanticAuthorityGrantedIsFalse = refl

publicationEffectIsFalse :
  publicationEffect canonicalRelationProducerBoundary ≡ false
publicationEffectIsFalse = refl

------------------------------------------------------------------------
-- Candidate syntax may later refine into legal semantic roles, but only through
-- an explicit context-resolution/admission witness.  The parser label itself
-- does not choose the role.
------------------------------------------------------------------------

data LegalRelationRole : Set where
  actorRole : LegalRelationRole
  objectRole : LegalRelationRole
  jurisdictionRole : LegalRelationRole
  evidenceRole : LegalRelationRole
  provenanceRole : LegalRelationRole
  qualifierRole : LegalRelationRole
  otherRelationRole : LegalRelationRole

record ContextualRelationResolution : Set where
  constructor contextualRelationResolution
  field
    sourceCandidate : RelationAttachmentCandidate
    resolvedRole : LegalRelationRole
    nonParserAuthority : Bool
    policyReferencePresent : Bool
    resolverReferencePresent : Bool

open ContextualRelationResolution public

record RelationResolutionAdmissionBoundary : Set where
  constructor relationResolutionAdmissionBoundary
  field
    parserLabelAloneChoosesLegalRole : Bool
    relationCandidateAloneAuthorizesAdmission : Bool
    contextualResolutionMayRefineCandidate : Bool
    directRuntimeNeedsSecondRelationalRuntime : Bool
    consumerParityMayIgnoreFineExecutionIdentity : Bool

canonicalRelationResolutionAdmissionBoundary : RelationResolutionAdmissionBoundary
canonicalRelationResolutionAdmissionBoundary =
  relationResolutionAdmissionBoundary
    false
    false
    true
    (Contextual.requiresSecondRelationalRuntime Contextual.canonicalDirectContextualBoundary)
    (Contextual.consumerParityCanIgnoreFineExecutionIdentity Contextual.canonicalDirectContextualBoundary)

parserLabelAloneDoesNotChooseLegalRole :
  parserLabelAloneChoosesLegalRole canonicalRelationResolutionAdmissionBoundary ≡ false
parserLabelAloneDoesNotChooseLegalRole = refl

relationCandidateAloneDoesNotAuthorizeAdmission :
  relationCandidateAloneAuthorizesAdmission canonicalRelationResolutionAdmissionBoundary ≡ false
relationCandidateAloneDoesNotAuthorizeAdmission = refl

noSecondRelationalRuntime :
  directRuntimeNeedsSecondRelationalRuntime canonicalRelationResolutionAdmissionBoundary ≡ false
noSecondRelationalRuntime = refl

consumerParityMayIgnoreFineExecution :
  consumerParityMayIgnoreFineExecutionIdentity canonicalRelationResolutionAdmissionBoundary ≡ true
consumerParityMayIgnoreFineExecution = refl

------------------------------------------------------------------------
-- Hard no-go types: structural parser relations do not promote themselves.
------------------------------------------------------------------------

data ParserPrepositionProvesJurisdiction : Set where
data ParserAgentMarkerProvesActor : Set where
data CandidateRelationAutomaticallyAdmitted : Set where

parserPrepositionDoesNotProveJurisdiction : ParserPrepositionProvesJurisdiction → ⊥
parserPrepositionDoesNotProveJurisdiction ()

parserAgentMarkerDoesNotProveActor : ParserAgentMarkerProvesActor → ⊥
parserAgentMarkerDoesNotProveActor ()

candidateRelationIsNotAutomaticallyAdmitted : CandidateRelationAutomaticallyAdmitted → ⊥
candidateRelationIsNotAutomaticallyAdmitted ()

-- Keep the existing admission owner visibly in the dependency graph: the new
-- producer supplies candidates only and does not replace its receipt currency.
existingAdmissionBoundaryStillBlocksParserAuthority :
  Admission.ParserCandidateAloneAuthorizesAdmission → ⊥
existingAdmissionBoundaryStillBlocksParserAuthority =
  Admission.parserCandidateAloneCannotAuthorizeAdmission
