module DASHI.Law.SensibLawLaterMedicalParticularHarmSourceConditionedExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- SOURCE-CONDITIONED PARTICULAR-HARM IDENTITY
--
-- Cross-pollination from the Atomic legal-test architecture:
--
--   source defining a legal/medical proposition
--     !=
--   source establishing its outcome in this case
--     !=
--   source establishing factual causation by a particular legal violation.
--
-- This owner is evidence/provenance structure only. It does not diagnose,
-- infer causation, or promote a later medical carrier into a Russell/QCAT
-- submission without an explicit submission witness.
------------------------------------------------------------------------

data HarmPropositionKind : Set where
  conditionIdentityProposition : HarmPropositionKind
  functionalImpactProposition : HarmPropositionKind
  temporalAggravationProposition : HarmPropositionKind
  factualCausationProposition : HarmPropositionKind


data MedicalSourceRole : Set where
  propositionDefinitionSource : MedicalSourceRole
  caseOutcomeSource : MedicalSourceRole
  submissionCarrierSource : MedicalSourceRole
  retrospectiveCrossReferenceSource : MedicalSourceRole

record SourceConditionedHarmAtom : Set₁ where
  constructor sourceConditionedHarmAtom
  field
    propositionKind : HarmPropositionKind
    propositionReference : String
    definingSourceReference : String
    outcomeSourceReference : String
    outcomeReceipt : Set
    atomReference : String

open SourceConditionedHarmAtom public

record LaterMedicalEvidence : Set₁ where
  constructor laterMedicalEvidence
  field
    carrierReference : String
    carrierDateReference : String
    sourceRole : MedicalSourceRole
    conditionAtoms : List SourceConditionedHarmAtom
    functionalAtoms : List SourceConditionedHarmAtom
    submissionRelationReference : String
    evidenceReceipt : Set

open LaterMedicalEvidence public

record ParticularHarmIdentityWeld : Set₁ where
  constructor particularHarmIdentityWeld
  field
    earlierClaimReference : String
    laterMedicalEvidence : LaterMedicalEvidence
    sameParticularHarmReceipt : Set
    weldReference : String

open ParticularHarmIdentityWeld public

record FactualCausationPromotionInput : Set₁ where
  constructor factualCausationPromotionInput
  field
    harmWeld : ParticularHarmIdentityWeld
    breachOrViolationReference : String
    causalMechanismOrButForReceipt : Set
    authorityReference : String

open FactualCausationPromotionInput public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ConditionIdentityAutomaticallySameClaimedInjury : Set where
data MedicalConditionAutomaticallyCausedByRussell : Set where
data LaterMedicalCarrierAutomaticallySubmittedToQCAT : Set where
data FunctionalLimitationAutomaticallyFactualCausation : Set where
data TemporalSequenceAutomaticallyAggravation : Set where

conditionIdentityDoesNotAutoIdentifyClaimedInjury :
  ConditionIdentityAutomaticallySameClaimedInjury → ⊥
conditionIdentityDoesNotAutoIdentifyClaimedInjury ()

medicalConditionDoesNotAutoEstablishRussellCausation :
  MedicalConditionAutomaticallyCausedByRussell → ⊥
medicalConditionDoesNotAutoEstablishRussellCausation ()

laterMedicalCarrierDoesNotAutoBecomeQCATSubmission :
  LaterMedicalCarrierAutomaticallySubmittedToQCAT → ⊥
laterMedicalCarrierDoesNotAutoBecomeQCATSubmission ()

functionalLimitationDoesNotAutoPayFactualCausation :
  FunctionalLimitationAutomaticallyFactualCausation → ⊥
functionalLimitationDoesNotAutoPayFactualCausation ()

temporalSequenceDoesNotAutoProveAggravation :
  TemporalSequenceAutomaticallyAggravation → ⊥
temporalSequenceDoesNotAutoProveAggravation ()

record LaterMedicalParticularHarmBoundary : Set where
  constructor laterMedicalParticularHarmBoundary
  field
    conditionIdentityMayBeEstablishedWithoutCausation : Bool
    conditionIdentityMayBeEstablishedWithoutCausationIsTrue :
      conditionIdentityMayBeEstablishedWithoutCausation ≡ true

    functionalImpactMayBeEstablishedWithoutCausation : Bool
    functionalImpactMayBeEstablishedWithoutCausationIsTrue :
      functionalImpactMayBeEstablishedWithoutCausation ≡ true

    sameParticularHarmRequiresExplicitWeld : Bool
    sameParticularHarmRequiresExplicitWeldIsTrue :
      sameParticularHarmRequiresExplicitWeld ≡ true

    factualCausationRequiresAdditionalReceipt : Bool
    factualCausationRequiresAdditionalReceiptIsTrue :
      factualCausationRequiresAdditionalReceipt ≡ true

    submissionRelationRequiresSeparateSource : Bool
    submissionRelationRequiresSeparateSourceIsTrue :
      submissionRelationRequiresSeparateSource ≡ true

canonicalLaterMedicalParticularHarmBoundary : LaterMedicalParticularHarmBoundary
canonicalLaterMedicalParticularHarmBoundary =
  laterMedicalParticularHarmBoundary
    true refl
    true refl
    true refl
    true refl
    true refl

------------------------------------------------------------------------
-- 30 June 2022 John Brown medical-report bounded fixture.
--
-- The recovered carrier is a Services Australia Carer Payment / Carer
-- Allowance medical report forwarded by John on 30 June 2022. Its medical
-- section records COPD, cPTSD and Dissociative Identity Disorder, requires
-- daily help because of disability/medical conditions, and records substantial
-- daily caring duties. It does not, on the recovered text, identify Russell or
-- state that Russell caused those conditions.
------------------------------------------------------------------------

john30Jun2022MedicalCarrier : String
john30Jun2022MedicalCarrier = "30.6.2022. J. Brown Med Report.pdf"

john30Jun2022COPDAtom : SourceConditionedHarmAtom
john30Jun2022COPDAtom =
  sourceConditionedHarmAtom
    conditionIdentityProposition
    "John Brown has COPD"
    "medical-condition vocabulary / treating-health-professional report"
    john30Jun2022MedicalCarrier
    ⊤
    "30-Jun-2022 COPD condition identity atom"

john30Jun2022CPTSDAtom : SourceConditionedHarmAtom
john30Jun2022CPTSDAtom =
  sourceConditionedHarmAtom
    conditionIdentityProposition
    "John Brown has cPTSD"
    "medical-condition vocabulary / treating-health-professional report"
    john30Jun2022MedicalCarrier
    ⊤
    "30-Jun-2022 cPTSD condition identity atom"

john30Jun2022DIDAtom : SourceConditionedHarmAtom
john30Jun2022DIDAtom =
  sourceConditionedHarmAtom
    conditionIdentityProposition
    "John Brown has Dissociative Identity Disorder"
    "medical-condition vocabulary / treating-health-professional report"
    john30Jun2022MedicalCarrier
    ⊤
    "30-Jun-2022 DID condition identity atom"

john30Jun2022DailyHelpAtom : SourceConditionedHarmAtom
john30Jun2022DailyHelpAtom =
  sourceConditionedHarmAtom
    functionalImpactProposition
    "daily help required because of disability/medical condition(s)"
    "Services Australia ADAT functional-impact question"
    john30Jun2022MedicalCarrier
    ⊤
    "30-Jun-2022 daily-help functional atom"

john30Jun2022MedicalEvidence : LaterMedicalEvidence
john30Jun2022MedicalEvidence =
  laterMedicalEvidence
    john30Jun2022MedicalCarrier
    "30 June 2022"
    caseOutcomeSource
    (john30Jun2022COPDAtom ∷ john30Jun2022CPTSDAtom ∷ john30Jun2022DIDAtom ∷ [])
    (john30Jun2022DailyHelpAtom ∷ [])
    "later Russell/QCAT submission relation unresolved; requires separate submission carrier witness"
    ⊤

record John30Jun2022MedicalFixture : Set where
  constructor john30Jun2022MedicalFixture
  field
    evidence : LaterMedicalEvidence
    medicalConditionIdentityEvidencePresent : Bool
    medicalConditionIdentityEvidencePresentIsTrue :
      medicalConditionIdentityEvidencePresent ≡ true
    functionalImpactEvidencePresent : Bool
    functionalImpactEvidencePresentIsTrue :
      functionalImpactEvidencePresent ≡ true
    russellNamedInRecoveredMedicalText : Bool
    russellNamedInRecoveredMedicalTextIsFalse :
      russellNamedInRecoveredMedicalText ≡ false
    russellCausationEstablishedByCarrier : Bool
    russellCausationEstablishedByCarrierIsFalse :
      russellCausationEstablishedByCarrier ≡ false
    laterQCATSubmissionRelationResolved : Bool
    laterQCATSubmissionRelationResolvedIsFalse :
      laterQCATSubmissionRelationResolved ≡ false

john30Jun2022MedicalFixture : John30Jun2022MedicalFixture
john30Jun2022MedicalFixture =
  john30Jun2022MedicalFixture
    john30Jun2022MedicalEvidence
    true refl
    true refl
    false refl
    false refl
    false refl
