module DASHI.Reasoning.IntergenerationalNameIntrusion where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.SymbolicTransformWithoutHomunculus as Symbolic
import DASHI.Reasoning.RelationalStateCore as Core

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- Corrected abstraction of partial family-name intrusions.
--
-- The base CorrectedNameIntrusion record is an observation carrier: it can
-- faithfully record uncertain or contradictory coding.  Claims that an event
-- was immediately corrected, non-composite and referentially distinct require
-- the validated subtype below.
--
-- Historical provenance:
-- * Sigmund Freud, The Psychopathology of Everyday Life (1901), no DOI.
-- Modern bounded comparators:
-- * Willem J. M. Levelt, Ardi Roelofs, Antje S. Meyer,
--   "A theory of lexical access in speech production" (1999),
--   DOI 10.1017/S0140525X99001776.
-- * Trevor A. Harley, Siobhan B. G. MacAndrew,
--   "Constraints Upon Word Substitution Speech Errors" (2001),
--   DOI 10.1023/A:1010421724343.
------------------------------------------------------------------------

data NameProductionStage : Set where
  conceptualActivation lemmaSelection phonologicalEncoding : NameProductionStage
  articulation monitoring correction : NameProductionStage

data IntrusionKind : Set where
  semanticAssociateIntrusion sharedFeatureIntrusion phonologicalIntrusion : IntrusionKind
  familyAssociationIntrusion undeterminedIntrusion : IntrusionKind

data InterpretationStatus : Set where
  historicalFreudianReading modernLexicalCompetitionReading : InterpretationStatus
  contextualHypothesisOnly noMotiveInference : InterpretationStatus

record NameCandidate : Set where
  constructor nameCandidate
  field
    candidateLabel : String
    referentRole : Core.RelationalRole
    activation : Nat
    affectiveSalience : Nat
    phonologicalOverlap : Nat

open NameCandidate public

record CorrectedNameIntrusion : Set where
  constructor correctedNameIntrusion
  field
    speaker intendedReferent competingReferent : Core.Participant
    intendedCandidate competingCandidate : NameCandidate
    emittedCompetingFragment : String
    finalIntendedName : String
    intrusionStage : NameProductionStage
    intrusionKind : IntrusionKind
    immediatelySelfCorrected : Bool
    currentFrustrationPresent : Bool
    historicalAssociationPresent : Bool
    deliberateCompositeLabelUsed : Bool
    intrusionReceipt : String

open CorrectedNameIntrusion public

------------------------------------------------------------------------
-- Validated corrected-intrusion subtype.
--
-- The role inequalities are stronger than comparing surface strings: the
-- intended and competing referents occupy distinct typed roles, and the
-- speaker is distinct from each referent in the coded episode.
------------------------------------------------------------------------

record ValidatedCorrectedNameIntrusion
    (event : CorrectedNameIntrusion) : Set where
  constructor validatedCorrectedNameIntrusion
  field
    immediateCorrectionProof : immediatelySelfCorrected event ≡ true
    nonCompositeProof : deliberateCompositeLabelUsed event ≡ false
    intendedCompetingRolesDistinct :
      referentRole (intendedCandidate event)
      ≢ referentRole (competingCandidate event)
    speakerIntendedRolesDistinct :
      Core.participantRole (speaker event)
      ≢ Core.participantRole (intendedReferent event)
    speakerCompetingRolesDistinct :
      Core.participantRole (speaker event)
      ≢ Core.participantRole (competingReferent event)
    intendedCandidateRoleMatchesReferent :
      referentRole (intendedCandidate event)
      ≡ Core.participantRole (intendedReferent event)
    competingCandidateRoleMatchesReferent :
      referentRole (competingCandidate event)
      ≡ Core.participantRole (competingReferent event)
    validationReceipt : String

open ValidatedCorrectedNameIntrusion public

record AssociativeTransportHypothesis : Set where
  constructor associativeTransportHypothesis
  field
    priorRelationshipTheme : String
    presentInteractionTheme : String
    sharedAffectiveFeature : String
    competingNameActivationIncreased : Bool
    stableIdentitySubstitutionEstablished : Bool
    hypothesisStatus : InterpretationStatus
    hypothesisReceipt : String

record NameIntrusionEvidenceBoundary : Set where
  field
    partialFalseStartProvesDeliberateComparison : Bool
    correctionProvesCompositeNickname : Bool
    oneSlipProvesStableProjection : Bool
    repeatedContextualPatternMaySupportHypothesis : Bool
    speechErrorAloneRecoversUnconsciousMotive : Bool
    modernLexicalCompetitionCompatible : Bool
    symbolicTransformRequiresHomunculus : Bool
    observationRecordAloneEstablishesCorrectedClassification : Bool
    boundaryNote : String

canonicalNameIntrusionEvidenceBoundary : NameIntrusionEvidenceBoundary
canonicalNameIntrusionEvidenceBoundary = record
  { partialFalseStartProvesDeliberateComparison = false
  ; correctionProvesCompositeNickname = false
  ; oneSlipProvesStableProjection = false
  ; repeatedContextualPatternMaySupportHypothesis = true
  ; speechErrorAloneRecoversUnconsciousMotive = false
  ; modernLexicalCompetitionCompatible = true
  ; symbolicTransformRequiresHomunculus =
      Symbolic.innerTranslatorRequired Symbolic.canonicalSymbolicCompromise
  ; observationRecordAloneEstablishesCorrectedClassification = false
  ; boundaryNote =
      "CorrectedNameIntrusion stores an observation. Only ValidatedCorrectedNameIntrusion proves immediate correction, non-composite use, distinct typed referents and candidate/referent role agreement. Even then, a family-association reading remains contextual and defeasible rather than proof of hidden intent."
  }

record IntergenerationalAssimilationRisk : Set where
  constructor intergenerationalAssimilationRisk
  field
    presentPerson historicalRelative : Core.Participant
    localResemblance : String
    resemblancePromotedToGlobalIdentity : Bool
    objectionTreatedAsConfirmation : Bool
    evidenceCorrectionChannelPresent : Bool
    riskReceipt : String

record PersonSpecificEvaluationInvariant : Set where
  field
    currentActEvaluatedOnCurrentEvidence : Bool
    historicalRelativeNotSubstitutedForCurrentPerson : Bool
    resemblanceDoesNotEntailIdentity : Bool
    rejectionOfAttributionDoesNotProveAttribution : Bool
    latestAccountDoesNotEraseEarlierVersions : Bool

canonicalPersonSpecificEvaluationInvariant : PersonSpecificEvaluationInvariant
canonicalPersonSpecificEvaluationInvariant = record
  { currentActEvaluatedOnCurrentEvidence = true
  ; historicalRelativeNotSubstitutedForCurrentPerson = true
  ; resemblanceDoesNotEntailIdentity = true
  ; rejectionOfAttributionDoesNotProveAttribution = true
  ; latestAccountDoesNotEraseEarlierVersions = true
  }
