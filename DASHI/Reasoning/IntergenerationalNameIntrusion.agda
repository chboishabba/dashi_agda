module DASHI.Reasoning.IntergenerationalNameIntrusion where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.SymbolicTransformWithoutHomunculus as Symbolic
import DASHI.Reasoning.RelationalStateCore as Core

------------------------------------------------------------------------
-- Corrected abstraction of partial family-name intrusions.
--
-- The phenomenon represented here is not a deliberate composite label such
-- as "relative-child".  It is a false start in which a competing family name
-- becomes partially active, is emitted, and is immediately corrected to the
-- intended name.  The formalism records lexical and affective competition but
-- does not infer hidden motive or a stable identity attribution.
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
  ; boundaryNote =
      "A partial competing-name intrusion is evidence of transient lexical competition. A family-association reading remains contextual and defeasible; it is not a composite label, diagnosis or proof of hidden intent."
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
