module DASHI.Cognition.PNF.SensibLawJudicialInstitutionalProductionContextExact where

------------------------------------------------------------------------
-- JUDICIAL INSTITUTIONAL PRODUCTION CONTEXT
--
-- This module does NOT encode a proposition that individual judges are biased,
-- corrupt, class-conscious, or acting in bad faith. It makes upstream social
-- and institutional context representable rather than assuming a neutral
-- oracle. Outcome-pattern evidence does not promote to subjective intent.
--
-- Sources / stable identifiers:
--   * Commonwealth of Australia Constitution Act, s 72 -- federal judicial
--     appointment/tenure architecture; canonical text at legislation.gov.au.
--   * Australian Constitution, Chapter III -- institutional location of federal
--     judicial power.
--   * Glen Sean Coulthard, Red Skin, White Masks: Rejecting the Colonial
--     Politics of Recognition (University of Minnesota Press, 2014),
--     ISBN 9780816679652 -- critical source for productive recognition/power.
--   * Robert Nichols, Theft Is Property! Dispossession and Critical Theory
--     (Duke University Press, 2020), publisher stable identifier/record:
--     https://www.dukeupress.edu/theft-is-property
--
-- Coulthard/Nichols proposition-level attribution is owned more narrowly by
-- SensibLawNativeTitleRecognitionCriticalSourceAtlasExact. The graph below is
-- DASHI synthesis and must not be back-attributed to either author.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawTypedLegalAuthorityEdgeExact as Edge
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as Operational

------------------------------------------------------------------------
-- Upstream production context is a typed input, not an unspoken constant.
------------------------------------------------------------------------

data ProductionContextKind : Set where
  culture
  schooling
  professionalFormation
  legalRecruitment
  professionalSelection
  judicialAppointment
  institutionalHistory
  educationalCanon
  appointmentStructure
  classComposition
  politicalContext
  dominantSocialNorms
  : ProductionContextKind

record ProductionContextReceipt : Set where
  constructor production-context-receipt
  field
    contextId : String
    kind : ProductionContextKind
    proposition : String
    source : Edge.SourceIdentity
    empiricalSupportRequired : Bool
    sourceSupportsThisExactProposition : Bool

open ProductionContextReceipt public

------------------------------------------------------------------------
-- Judicial independence / democratic accountability are non-identical axes.
------------------------------------------------------------------------

data InstitutionalAxis : Set where
  decisionalIndependence
  electoralAccountability
  appellateAccountability
  reasonsGiving
  legislativeOverrideSubjectToConstitution
  constitutionalAuthorization
  democraticLegitimacy
  : InstitutionalAxis

data IntentionalDesignImpliesNormativeJustification : Set where
data JudicialIndependenceImpliesDemocraticAccountability : Set where
data ConstitutionalAuthorizationImpliesDemocraticLegitimacyEveryExercise : Set where
data AppellateRecourseEqualsPopularPoliticalRecourse : Set where

intentionalDesignDoesNotProveJustification :
  IntentionalDesignImpliesNormativeJustification → ⊥
intentionalDesignDoesNotProveJustification ()

independenceDoesNotEqualDemocraticAccountability :
  JudicialIndependenceImpliesDemocraticAccountability → ⊥
independenceDoesNotEqualDemocraticAccountability ()

constitutionalAuthorizationDoesNotCloseLegitimacyQuestion :
  ConstitutionalAuthorizationImpliesDemocraticLegitimacyEveryExercise → ⊥
constitutionalAuthorizationDoesNotCloseLegitimacyQuestion ()

appealIsNotPopularElection : AppellateRecourseEqualsPopularPoliticalRecourse → ⊥
appealIsNotPopularElection ()

------------------------------------------------------------------------
-- Reasons, applied rule, and effect remain separate observables.
------------------------------------------------------------------------

record DecisionAnalysis : Set where
  constructor decision-analysis
  field
    claimedLegalReason : String
    decisionRuleReconstructed : String
    distributionalEffect : String
    authorityForClaimedReason : Edge.SourceIdentity
    reconstructedRuleIsDashInference : Bool
    distributionalEffectIsEmpiricalOrFormalOutput : Bool

open DecisionAnalysis public

data ClaimedReasonDeterminesActualDecisionRule : Set where
data ClaimedReasonDeterminesDistributionalEffect : Set where
data DistributionalPatternProvesSubjectiveBias : Set where
data GoodFaithDoctrineImpliesNonHegemonicEffect : Set where
data IndividualImpartialityImpliesSystemOutputNeutrality : Set where

claimedReasonDoesNotDetermineAppliedRuleByDefinition :
  ClaimedReasonDeterminesActualDecisionRule → ⊥
claimedReasonDoesNotDetermineAppliedRuleByDefinition ()

claimedReasonDoesNotDetermineEffectByDefinition :
  ClaimedReasonDeterminesDistributionalEffect → ⊥
claimedReasonDoesNotDetermineEffectByDefinition ()

patternDoesNotProveSubjectiveBias : DistributionalPatternProvesSubjectiveBias → ⊥
patternDoesNotProveSubjectiveBias ()

goodFaithDoesNotProveNonHegemonicEffect : GoodFaithDoctrineImpliesNonHegemonicEffect → ⊥
goodFaithDoesNotProveNonHegemonicEffect ()

individualImpartialityDoesNotProveSystemNeutrality :
  IndividualImpartialityImpliesSystemOutputNeutrality → ⊥
individualImpartialityDoesNotProveSystemNeutrality ()

------------------------------------------------------------------------
-- A source-backed stated rationale and an observed distributional effect are
-- intentionally stored in different coordinates.
------------------------------------------------------------------------

record RationaleEffectPair : Set where
  constructor rationale-effect-pair
  field
    statedRationale : String
    rationaleAuthority : Edge.SourceIdentity
    observedOrComputedEffect : String
    effectSourceOrMethod : String
    effectPromotedToJudgeIntent : Bool
    effectPromotedToJudgeIntentIsFalse : effectPromotedToJudgeIntent ≡ false

open RationaleEffectPair public

------------------------------------------------------------------------
-- Selection/socialisation hypotheses require receipts; they are not axioms.
------------------------------------------------------------------------

data NonRandomRecruitmentProvesDoctrinalBias : Set where
data CulturalEmbeddednessProvesCaseOutcome : Set where
data ProfessionalFormationErasesAgency : Set where

selectionDoesNotAutomaticallyProveDoctrinalBias :
  NonRandomRecruitmentProvesDoctrinalBias → ⊥
selectionDoesNotAutomaticallyProveDoctrinalBias ()

cultureDoesNotAutomaticallyDetermineOutcome : CulturalEmbeddednessProvesCaseOutcome → ⊥
cultureDoesNotAutomaticallyDetermineOutcome ()

formationDoesNotEraseAgency : ProfessionalFormationErasesAgency → ⊥
formationDoesNotEraseAgency ()

------------------------------------------------------------------------
-- Operational systems bridge: observed operation can be analysed without
-- converting repeated effects directly into subjective intent.
------------------------------------------------------------------------

operationalEffectDoesNotAutomaticallyProveIntent :
  Operational.POSIWIDProvesHostileIntent → ⊥
operationalEffectDoesNotAutomaticallyProveIntent =
  Operational.posiwidDoesNotProveHostileIntent
