module DASHI.Law.SensibLawTemporalHealthEvidenceWrongTypeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWrongTypeCausationElementExact as Element

------------------------------------------------------------------------
-- TEMPORAL HEALTH EVIDENCE -> WRONGTYPE CAUSATION BOUNDARY
--
-- DASHI-original evidence compiler.
--
-- Purpose:
--   preserve timestamped physiological observations, contemporaneous notes,
--   legal/dispute events, and submitted evidentiary carriers without silently
--   promoting temporal association into factual causation, scope, liability,
--   or a medical diagnosis.
--
-- This owner is deliberately generic.  The QCAT 0096/22 fixture below records
-- only carrier/page/event identities needed to regression-test the boundary;
-- it does not encode private measurement values or create medical conclusions.
------------------------------------------------------------------------

data HealthEvidenceKind : Set where
  physiologicalMeasurement : HealthEvidenceKind
  contemporaneousHealthNote : HealthEvidenceKind
  submittedHealthTable : HealthEvidenceKind
  submittedHealthChart : HealthEvidenceKind
  submittedInjuryNarrative : HealthEvidenceKind
  derivedTemporalRelation : HealthEvidenceKind


data TemporalRelationKind : Set where
  exactTimestampRelation : TemporalRelationKind
  sameDayRelation : TemporalRelationKind
  boundedWindowRelation : TemporalRelationKind
  temporalRelationUnresolved : TemporalRelationKind


record HealthObservation : Set₁ where
  constructor healthObservation
  field
    participantReference : String
    observationTimeReference : String
    metricReference : String
    valueReference : String
    evidenceKind : HealthEvidenceKind
    sourceCarrierReference : String
    observationReceipt : Set

open HealthObservation public

record DisputeEvent : Set₁ where
  constructor disputeEvent
  field
    eventTimeReference : String
    eventReference : String
    eventCarrierReference : String
    eventReceipt : Set

open DisputeEvent public

record SubmittedHealthCarrier : Set₁ where
  constructor submittedHealthCarrier
  field
    bundleReference : String
    pageReference : String
    embeddedEvidenceReference : String
    evidenceKind : HealthEvidenceKind
    embeddedInBundleReceipt : Set
    carrierReference : String

open SubmittedHealthCarrier public

record TemporalHealthCorrelation
    (observation : HealthObservation)
    (event : DisputeEvent) : Set₁ where
  constructor temporalHealthCorrelation
  field
    relation : TemporalRelationKind
    relationReceipt : Set
    correlationReference : String

open TemporalHealthCorrelation public

------------------------------------------------------------------------
-- SensibLaw / WrongType intersection.
--
-- A correlation bundle may be admitted as evidence for an exact live
-- WrongType causation element.  It does not pay that element.  Payment remains
-- the existing FactualCausationElementPayment constructor, with its but-for or
-- exceptional causation receipt and same-object weld requirements.
------------------------------------------------------------------------

record WrongTypeTemporalHealthEvidence
    {declaration : Element.WrongTypeCausationElementDeclaration}
    (weld : Element.ViolationWrongTypeCausationElementWeld declaration) : Set₁ where
  constructor wrongTypeTemporalHealthEvidence
  field
    submittedCarriers : List SubmittedHealthCarrier
    observationReferences : List String
    eventReferences : List String
    correlationReferences : List String
    sameWrongTypeAndElementWeld :
      Element.ViolationWrongTypeCausationElementWeld declaration
    sameWeldReceipt : sameWrongTypeAndElementWeld ≡ weld
    evidenceReference : String

open WrongTypeTemporalHealthEvidence public

record TemporalHealthEvidencePayment
    {declaration : Element.WrongTypeCausationElementDeclaration}
    {weld : Element.ViolationWrongTypeCausationElementWeld declaration}
    (evidence : WrongTypeTemporalHealthEvidence weld) : Set₁ where
  constructor temporalHealthEvidencePayment
  field
    factualPayment : Element.FactualCausationElementPayment weld
    evidenceConsideredReceipt : Set
    paymentReference : String

open TemporalHealthEvidencePayment public

------------------------------------------------------------------------
-- Evidence-state classifier.
------------------------------------------------------------------------

data TemporalHealthEvidenceState : Set where
  carrierPresent : TemporalHealthEvidenceState
  temporallyCorrelated : TemporalHealthEvidenceState
  admittedToWrongTypeElement : TemporalHealthEvidenceState
  factualCausationPaid : TemporalHealthEvidenceState


record TemporalHealthEvidenceBoundary : Set where
  constructor temporalHealthEvidenceBoundary
  field
    submittedChartAutomaticallyPaysCausation : Bool
    submittedChartAutomaticallyPaysCausationIsFalse :
      submittedChartAutomaticallyPaysCausation ≡ false

    sameDayCorrelationAutomaticallyPaysCausation : Bool
    sameDayCorrelationAutomaticallyPaysCausationIsFalse :
      sameDayCorrelationAutomaticallyPaysCausation ≡ false

    contemporaneousNoteAutomaticallyPaysCausation : Bool
    contemporaneousNoteAutomaticallyPaysCausationIsFalse :
      contemporaneousNoteAutomaticallyPaysCausation ≡ false

    requestedDamagesAutomaticallyEstablishScope : Bool
    requestedDamagesAutomaticallyEstablishScopeIsFalse :
      requestedDamagesAutomaticallyEstablishScope ≡ false

    measurementAutomaticallyCreatesMedicalDiagnosis : Bool
    measurementAutomaticallyCreatesMedicalDiagnosisIsFalse :
      measurementAutomaticallyCreatesMedicalDiagnosis ≡ false

    factualPaymentStillRequiresWrongTypePayment : Bool
    factualPaymentStillRequiresWrongTypePaymentIsTrue :
      factualPaymentStillRequiresWrongTypePayment ≡ true

canonicalTemporalHealthEvidenceBoundary : TemporalHealthEvidenceBoundary
canonicalTemporalHealthEvidenceBoundary =
  temporalHealthEvidenceBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl

------------------------------------------------------------------------
-- Firewalls: category mismatches are uninhabited.
------------------------------------------------------------------------

data SubmittedChartAutomaticallyCausation : Set where
data SameDayCorrelationAutomaticallyCausation : Set where
data ContemporaneousNoteAutomaticallyCausation : Set where
data RequestedDamagesAutomaticallyScope : Set where
data MeasurementAutomaticallyDiagnosis : Set where
data CorrelationAutomaticallyParticularHarmIdentity : Set where

submittedChartDoesNotAutoCause :
  SubmittedChartAutomaticallyCausation → ⊥
submittedChartDoesNotAutoCause ()

sameDayCorrelationDoesNotAutoCause :
  SameDayCorrelationAutomaticallyCausation → ⊥
sameDayCorrelationDoesNotAutoCause ()

contemporaneousNoteDoesNotAutoCause :
  ContemporaneousNoteAutomaticallyCausation → ⊥
contemporaneousNoteDoesNotAutoCause ()

requestedDamagesDoNotAutoEstablishScope :
  RequestedDamagesAutomaticallyScope → ⊥
requestedDamagesDoNotAutoEstablishScope ()

measurementDoesNotAutoDiagnose :
  MeasurementAutomaticallyDiagnosis → ⊥
measurementDoesNotAutoDiagnose ()

correlationDoesNotIdentifyParticularHarm :
  CorrelationAutomaticallyParticularHarmIdentity → ⊥
correlationDoesNotIdentifyParticularHarm ()

------------------------------------------------------------------------
-- QCAT 0096/22 regression fixture.
--
-- These strings pin only provenance coordinates already present in the final
-- evidentiary bundle: the final carrier, pages 82-83 health charts/tables, and
-- selected dispute-event dates.  No physiological values are encoded here.
------------------------------------------------------------------------

qcat0096FinalBundle : String
qcat0096FinalBundle = "QCAT:0096/22 final annotated Russell evidentiary bundle"

qcat0096HealthPages : String
qcat0096HealthPages = "pages 82-83 health tables/charts"

qcat0096HealthNarrative : String
qcat0096HealthNarrative = "submitted hypertension/injury narrative"

qcat0096Event26Jan : String
qcat0096Event26Jan = "2022-01-26 notice/breach sequence"

qcat0096Event04Feb : String
qcat0096Event04Feb = "2022-02-04 inspection"

qcat0096Event14Feb : String
qcat0096Event14Feb = "2022-02-14 notice-to-leave and breach sequence"

qcat0096Event16Feb : String
qcat0096Event16Feb = "2022-02-16 inspection-of-breach sequence"

record QCAT0096TemporalHealthFixture : Set₁ where
  constructor qcat0096TemporalHealthFixture
  field
    finalBundleReference : String
    healthPagesReference : String
    narrativeReference : String
    eventReferences : List String

    healthEvidenceEmbeddedInFinalBundle : Set
    disputeEventsPresentInSameBundle : Set

    temporalCorrelationMayBeRecorded : Bool
    temporalCorrelationMayBeRecordedIsTrue :
      temporalCorrelationMayBeRecorded ≡ true

    temporalCorrelationPaysCausation : Bool
    temporalCorrelationPaysCausationIsFalse :
      temporalCorrelationPaysCausation ≡ false

open QCAT0096TemporalHealthFixture public

qcat0096Fixture :
  (embeddedReceipt : Set) →
  (eventReceipt : Set) →
  QCAT0096TemporalHealthFixture
qcat0096Fixture embeddedReceipt eventReceipt =
  qcat0096TemporalHealthFixture
    qcat0096FinalBundle
    qcat0096HealthPages
    qcat0096HealthNarrative
    (qcat0096Event26Jan ∷
     qcat0096Event04Feb ∷
     qcat0096Event14Feb ∷
     qcat0096Event16Feb ∷ [])
    embeddedReceipt
    eventReceipt
    true refl
    false refl
