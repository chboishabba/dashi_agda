module DASHI.Law.AustralianFamilyLawOrderInteractionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution

------------------------------------------------------------------------
-- AUSTRALIAN FAMILY-LAW ORDER INTERACTION
--
-- The operational interaction is not represented by a single supremacy flag.
-- Division 11 of Part VII provides specific mechanisms for inconsistent federal
-- family-law orders/injunctions and State/Territory family-violence orders.
-- Subdivision DA separately provides court-driven information-sharing routes.
-- Child-welfare law/jurisdiction remains a distinct coordinate.
------------------------------------------------------------------------

data LegalOrderKind : Set where
  federalParentingOrder : LegalOrderKind
  federalRecoveryOrOtherChildTimeOrder : LegalOrderKind
  federalFamilyLawInjunction : LegalOrderKind
  stateTerritoryFamilyViolenceOrder : LegalOrderKind
  childWelfareOrder : LegalOrderKind

data OrderInteractionMechanism : Set where
  section68PConsistencyAndNotice : OrderInteractionMechanism
  section68QInvalidityToExtentOfInconsistency : OrderInteractionMechanism
  section68RReviveVaryDischargeSuspend : OrderInteractionMechanism
  section68SProcedure : OrderInteractionMechanism
  section68TInterimFamilyViolenceOrderProcedure : OrderInteractionMechanism
  subdivisionDAInformationSharing : OrderInteractionMechanism

data InformationSharingStage : Set where
  informationExistsAtAgency : InformationSharingStage
  particularsOrderMade : InformationSharingStage
  productionOrderMade : InformationSharingStage
  agencyResponseProvided : InformationSharingStage
  courtReceivedInformation : InformationSharingStage
  admittedIntoEvidence : InformationSharingStage
  evidentialWeightAssessed : InformationSharingStage

------------------------------------------------------------------------
-- Primary source atlas.
------------------------------------------------------------------------

familyLawDivision11Source : Attribution.AttributedSource
familyLawDivision11Source = Attribution.mkNoDOISource
  "Commonwealth of Australia"
  "Family Law Act 1975, Part VII Division 11—Family violence, sections 68N-68T"
  "Federal Register of Legislation"
  "current compilation surface searched 2026-09-14"
  "https://www.legislation.gov.au/C2004A00275/latest/text"
  Attribution.governmentSource
  "primary statutory source for the operational interaction of specified federal orders/injunctions and existing or proposed State/Territory family-violence orders; citation does not decide any concrete inconsistency"
  Attribution.publicAttribution

familyLawInformationSharingSource : Attribution.AttributedSource
familyLawInformationSharingSource = Attribution.mkNoDOISource
  "Commonwealth of Australia"
  "Family Law Act 1975, Part VII Subdivision DA—Orders for information etc. in child-related proceedings"
  "Federal Register of Legislation"
  "current compilation surface searched 2026-09-14"
  "https://www.legislation.gov.au/C2004A00275/latest/text"
  Attribution.governmentSource
  "primary statutory source for court orders seeking particulars/documents/information from information-sharing agencies; existence of the route does not prove information exists, was requested, received, admitted or correctly weighted"
  Attribution.publicAttribution

attorneyGeneralInformationSharingSource : Attribution.AttributedSource
attorneyGeneralInformationSharingSource = Attribution.mkNoDOISource
  "Australian Government Attorney-General's Department"
  "Family Law Information Sharing"
  "Attorney-General's Department"
  "current page searched 2026-09-14"
  "https://www.ag.gov.au/families-and-marriage/families/family-law-information-sharing"
  Attribution.governmentSource
  "implementation/context source confirming the Family Law Amendment (Information Sharing) Act 2023 commenced 6 May 2024 and introduced the court-driven Subdivision DA framework; does not create case-level information custody or evidential weight"
  Attribution.publicAttribution

queenslandDVOFamilyLawInteractionSource : Attribution.AttributedSource
queenslandDVOFamilyLawInteractionSource = Attribution.mkNoDOISource
  "State of Queensland"
  "Domestic and Family Violence Protection Act 2012, Division 7—Relationship between domestic violence orders and family law orders, sections 77-78"
  "Queensland Legislation"
  "in-force 2026 surface searched 2026-09-14"
  "https://www.legislation.qld.gov.au/view/whole/html/inforce/current/act-2012-005"
  Attribution.governmentSource
  "State-level manifestation requiring disclosure/consideration of family-law orders and directing attention to the Commonwealth section 68R power; it does not alter the source or scope of the federal power"
  Attribution.publicAttribution

orderInteractionSourceAtlas : Attribution.AttributedSourceAtlas
orderInteractionSourceAtlas = Attribution.mkSourceAtlas
  "Australian family-law order interaction source atlas"
  "DASHI.Law.AustralianFamilyLawOrderInteractionExact"
  (familyLawDivision11Source
    ∷ familyLawInformationSharingSource
    ∷ attorneyGeneralInformationSharingSource
    ∷ queenslandDVOFamilyLawInteractionSource
    ∷ [])
  "federal statutory mechanisms + information-sharing context + Queensland manifestation; no source citation itself decides inconsistency, jurisdiction, admissibility, weight or case outcome"

------------------------------------------------------------------------
-- Source-paid structural coordinates.
------------------------------------------------------------------------

section68QInvalidityIsToExtentOfInconsistency : Bool
section68QInvalidityIsToExtentOfInconsistency = true

section68RStateTerritoryVariationPowerLocated : Bool
section68RStateTerritoryVariationPowerLocated = true

subdivisionDAInformationSharingLocated : Bool
subdivisionDAInformationSharingLocated = true

childProtectionJurisdictionSeparatelyTyped : Bool
childProtectionJurisdictionSeparatelyTyped = true

------------------------------------------------------------------------
-- Operational interaction receipt.  The receipt identifies the mechanism and
-- whether its factual/application predicates have actually been paid.
------------------------------------------------------------------------

record OrderInteractionReceipt : Set where
  constructor orderInteractionReceipt
  field
    federalOrderReference : String
    familyViolenceOrderReference : String
    federalOrderKind : LegalOrderKind
    inconsistencyQuestionRaised : Bool
    inconsistencyEstablished : Bool
    section68QEffectApplied : Bool
    section68RPowerAvailable : Bool
    section68RPowerActuallyExercised : Bool
    childWelfareOrderOrProceedingReference : String
    childProtectionJurisdictionEvaluated : Bool

open OrderInteractionReceipt public

------------------------------------------------------------------------
-- Information-sharing receipt.  Each stage is retained independently.
------------------------------------------------------------------------

record InformationSharingReceipt : Set where
  constructor informationSharingReceipt
  field
    agencyReference : String
    informationCategoryReference : String
    existsAtAgencyPaid : Bool
    particularsOrderPaid : Bool
    productionOrderPaid : Bool
    agencyResponsePaid : Bool
    courtReceiptPaid : Bool
    admissionPaid : Bool
    weightAssessmentPaid : Bool

open InformationSharingReceipt public

------------------------------------------------------------------------
-- WrongType / promotion firewalls.
------------------------------------------------------------------------

data CommonwealthSupremacyAutomaticallyCompleteOperationalRule : Set where
data InconsistencyAutomaticallyInvalidatesWholeFamilyViolenceOrder : Set where
data Section68RPowerAutomaticallyExercised : Set where
data InformationExistsAutomaticallyReceivedByCourt : Set where
data CourtReceiptAutomaticallyAdmitted : Set where
data CourtReceiptAutomaticallyCorrectWeight : Set where
data FamilyProceedingAutomaticallyDisplacesChildProtectionJurisdiction : Set where
data StateFamilyViolenceOrderAutomaticallyDeterminesFederalParentingQuestion : Set where
data FederalParentingOrderAutomaticallyErasesEveryStateProtection : Set where

commonwealthSupremacyDoesNotAutomaticallyCompleteOperationalRule :
  CommonwealthSupremacyAutomaticallyCompleteOperationalRule → ⊥
commonwealthSupremacyDoesNotAutomaticallyCompleteOperationalRule ()

inconsistencyDoesNotAutomaticallyInvalidateWholeFamilyViolenceOrder :
  InconsistencyAutomaticallyInvalidatesWholeFamilyViolenceOrder → ⊥
inconsistencyDoesNotAutomaticallyInvalidateWholeFamilyViolenceOrder ()

section68RPowerDoesNotAutomaticallyExerciseItself :
  Section68RPowerAutomaticallyExercised → ⊥
section68RPowerDoesNotAutomaticallyExerciseItself ()

informationExistenceDoesNotAutomaticallyMeanCourtReceipt :
  InformationExistsAutomaticallyReceivedByCourt → ⊥
informationExistenceDoesNotAutomaticallyMeanCourtReceipt ()

courtReceiptDoesNotAutomaticallyMeanAdmission :
  CourtReceiptAutomaticallyAdmitted → ⊥
courtReceiptDoesNotAutomaticallyMeanAdmission ()

courtReceiptDoesNotAutomaticallyMeanCorrectWeight :
  CourtReceiptAutomaticallyCorrectWeight → ⊥
courtReceiptDoesNotAutomaticallyMeanCorrectWeight ()

familyProceedingDoesNotAutomaticallyDisplaceChildProtectionJurisdiction :
  FamilyProceedingAutomaticallyDisplacesChildProtectionJurisdiction → ⊥
familyProceedingDoesNotAutomaticallyDisplaceChildProtectionJurisdiction ()

stateFamilyViolenceOrderDoesNotAutomaticallyDetermineFederalParentingQuestion :
  StateFamilyViolenceOrderAutomaticallyDeterminesFederalParentingQuestion → ⊥
stateFamilyViolenceOrderDoesNotAutomaticallyDetermineFederalParentingQuestion ()

federalParentingOrderDoesNotAutomaticallyEraseEveryStateProtection :
  FederalParentingOrderAutomaticallyErasesEveryStateProtection → ⊥
federalParentingOrderDoesNotAutomaticallyEraseEveryStateProtection ()

record AustralianFamilyLawOrderInteractionBoundary : Set where
  constructor australianFamilyLawOrderInteractionBoundary
  field
    division11MechanismsRetained : Bool
    section68QExtentLimited : Bool
    section68RPowerSeparatedFromExercise : Bool
    informationSharingStagesSeparated : Bool
    childProtectionJurisdictionSeparate : Bool
    bareSupremacySloganCompleteOperationalRule : Bool
    wholeFamilyViolenceOrderAutomaticallyInvalid : Bool
    informationExistenceEqualsCourtReceipt : Bool
    courtReceiptEqualsCorrectWeight : Bool
    familyProceedingDisplacesChildProtection : Bool
    citationDecidesConcreteCase : Bool

open AustralianFamilyLawOrderInteractionBoundary public

canonicalAustralianFamilyLawOrderInteractionBoundary :
  AustralianFamilyLawOrderInteractionBoundary
canonicalAustralianFamilyLawOrderInteractionBoundary =
  australianFamilyLawOrderInteractionBoundary
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
