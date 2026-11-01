module DASHI.Culture.AnthropologyEthnographicFieldworkReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- ANTHROPOLOGY ETHNOGRAPHIC FIELDWORK RECEIPT
--
-- Method source:
-- Signe Howell, "Ethnography", Open Encyclopedia of Anthropology,
-- first published 2018, updated edition 2023.
-- DOI: 10.29164/18ethno
--
-- Cross-check surface:
-- American Anthropological Association, Perspectives: An Open Introduction to
-- Cultural Anthropology, Fieldwork chapter: ethnography, observation and
-- participant observation as core anthropological data-gathering practices.
--
-- This module formalises the receipt SHAPE only.  It does not claim that any
-- DASHI anthropology claim has been established by fieldwork until an actual
-- producer supplies the corresponding provenance-bearing observation record.
------------------------------------------------------------------------

data EthnographicPerspective : Set where
  emic : EthnographicPerspective
  etic : EthnographicPerspective
  mixedPerspective : EthnographicPerspective

data FieldworkRelation : Set where
  participantObservation : FieldworkRelation
  observationOnly : FieldworkRelation
  interview : FieldworkRelation
  documentaryArtifact : FieldworkRelation
  mixedMethod : FieldworkRelation

record EthnographicSource : Set where
  constructor ethnographic-source
  field
    author : String
    title : String
    sourceId : String
    sourceRole : String
open EthnographicSource public

howellEthnographySource : EthnographicSource
howellEthnographySource =
  ethnographic-source
    "Signe Howell"
    "Ethnography"
    "doi:10.29164/18ethno"
    "methodological source; not an empirical receipt for any DASHI community"

record EthnographicFieldworkReceipt : Set where
  constructor ethnographic-fieldwork-receipt
  field
    researchQuestion : String
    communityOrField : String
    place : String
    timeSpan : String
    researcher : String
    relation : FieldworkRelation
    perspective : EthnographicPerspective
    localLanguageOrTerms : String
    observationCarrier : String
    interviewCarrier : String
    documentaryCarrier : String
    fieldNotesCarrier : String
    consentOrAuthorityCarrier : String
    ethicsBoundary : String
    reflexivePosition : String
    sourceProvenance : String
    communityPerspectiveRetained : Bool
    researcherInterpretationSeparated : Bool
    observedPracticeSeparatedFromReportedPractice : Bool
    appendOnlyEvidence : Bool
open EthnographicFieldworkReceipt public

------------------------------------------------------------------------
-- Admission boundary: generic observer data are not automatically
-- ethnographic.  The method requires situated, provenance-bearing fieldwork
-- and explicit separation of community perspective from researcher reading.
------------------------------------------------------------------------

record EthnographicAdmission : Set where
  constructor ethnographic-admission
  field
    receipt : EthnographicFieldworkReceipt
    fieldContextBound : Bool
    temporalContextBound : Bool
    methodDeclared : Bool
    provenanceBound : Bool
    ethicsOrAuthorityBound : Bool
    perspectiveBoundaryExplicit : Bool
    empiricalPromotionAllowed : Bool
open EthnographicAdmission public

record EthnographicMethodBoundary : Set where
  constructor ethnographic-method-boundary
  field
    methodContractPaid : Bool
    concreteFieldworkProducerPaid : Bool
    participantObservationRequiredForEveryAnthropologySubfield : Bool
    sourceMethodCreatesEmpiricalFinding : Bool
    genericObserverCreatesEthnography : Bool
open EthnographicMethodBoundary public

canonicalEthnographicMethodBoundary : EthnographicMethodBoundary
canonicalEthnographicMethodBoundary =
  ethnographic-method-boundary true false false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data GenericObserverCreatesEthnographicReceipt : Set where
data MethodSourceCreatesFieldworkEvidence : Set where
data ResearcherInterpretationEqualsCommunityPerspective : Set where
data ReportedPracticeEqualsObservedPractice : Set where

genericObserverIsNotEthnographicReceipt :
  GenericObserverCreatesEthnographicReceipt → ⊥
genericObserverIsNotEthnographicReceipt ()

methodSourceIsNotFieldworkEvidence :
  MethodSourceCreatesFieldworkEvidence → ⊥
methodSourceIsNotFieldworkEvidence ()

researcherReadingIsNotCommunityPerspective :
  ResearcherInterpretationEqualsCommunityPerspective → ⊥
researcherReadingIsNotCommunityPerspective ()

reportedPracticeIsNotObservedPractice :
  ReportedPracticeEqualsObservedPractice → ⊥
reportedPracticeIsNotObservedPractice ()
