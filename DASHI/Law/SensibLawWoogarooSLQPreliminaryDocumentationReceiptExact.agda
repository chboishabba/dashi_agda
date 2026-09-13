module DASHI.Law.SensibLawWoogarooSLQPreliminaryDocumentationReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- STATE LIBRARY OF QUEENSLAND PRELIMINARY-DOCUMENTATION ACQUISITION RECEIPT
--
-- Source basis: State Library of Queensland OneSearch record 99184900524002061.
-- This owner records existence, bibliographic identity, physical availability
-- and volume structure of the EPBC 2019/8575 Preliminary Documentation set.
-- It does not import any substantive ecological proposition from those volumes
-- until the relevant pages/tables/maps are actually inspected and cited.
------------------------------------------------------------------------

data PDVolume : Set where
  partAiPreliminaryDocumentationReport : PDVolume
  partAiiVegetationClearingFaunaManagementPlanClearingDirections : PDVolume
  partAiiiAttachmentA15 : PDVolume
  partBReferralMaterial : PDVolume

record SLQPreliminaryDocumentationReceipt : Set where
  constructor slq-preliminary-documentation-receipt
  field
    epbcReference : String
    title : String
    author : String
    commissioningBody : String
    publisher : String
    creationYear : String
    recordNumber : String
    location : String
    accessCondition : String
    formatDescription : String
    volumeCount : Nat
    firstVolume : PDVolume
    secondVolume : PDVolume
    thirdVolume : PDVolume
    fourthVolume : PDVolume
    sourceReference : String
    physicalSetExists : Bool
    physicalSetExistsIsTrue : physicalSetExists ≡ true
    substantiveEcologyExtracted : Bool
    substantiveEcologyExtractedIsFalse : substantiveEcologyExtracted ≡ false

open SLQPreliminaryDocumentationReceipt public

springfield8575SLQReceipt : SLQPreliminaryDocumentationReceipt
springfield8575SLQReceipt = slq-preliminary-documentation-receipt
  "EPBC 2019/8575"
  "Springfield residential development Mur Boulevard, Springfield Qld : preliminary documentation report"
  "Saunders Havill Group"
  "Cherish Enterprises"
  "Saunders Havill Group, Bowen Hills, Queensland"
  "2026"
  "99184900524002061"
  "State Library of Queensland, John Oxley Collection, Level 4"
  "Onsite only; in storage; request to access from Level 4; shelf/reference JEIS1987"
  "4 volumes : illustrations, charts, maps ; 30 cm"
  4
  partAiPreliminaryDocumentationReport
  partAiiVegetationClearingFaunaManagementPlanClearingDirections
  partAiiiAttachmentA15
  partBReferralMaterial
  "State Library of Queensland OneSearch record 99184900524002061"
  true refl
  false refl

------------------------------------------------------------------------
-- Acquisition plan: named volumes map to named legal consumers.
------------------------------------------------------------------------

data ExtractionTarget : Set where
  exactProjectFootprint : ExtractionTarget
  habitatAreaTables : ExtractionTarget
  habitatQualityScoring : ExtractionTarget
  speciesSurveyUse : ExtractionTarget
  clearingDirections : ExtractionTarget
  retainedHabitat : ExtractionTarget
  connectivityFragmentation : ExtractionTarget
  avoidanceMitigation : ExtractionTarget
  offsets : ExtractionTarget
  referralBaseline : ExtractionTarget

record VolumeExtractionDemand : Set where
  constructor volume-extraction-demand
  field
    volume : PDVolume
    target : ExtractionTarget
    federalConsumer : Bool
    queenslandS13Consumer : Bool
    queenslandS102Consumer : Bool
    sourceMustBePageLocated : Bool

open VolumeExtractionDemand public

partAiHabitatTablesDemand : VolumeExtractionDemand
partAiHabitatTablesDemand = volume-extraction-demand
  partAiPreliminaryDocumentationReport habitatAreaTables true true true true

partAiConnectivityDemand : VolumeExtractionDemand
partAiConnectivityDemand = volume-extraction-demand
  partAiPreliminaryDocumentationReport connectivityFragmentation true true true true

partAiiClearingDirectionsDemand : VolumeExtractionDemand
partAiiClearingDirectionsDemand = volume-extraction-demand
  partAiiVegetationClearingFaunaManagementPlanClearingDirections clearingDirections true true true true

partAiiiHabitatQualityDemand : VolumeExtractionDemand
partAiiiHabitatQualityDemand = volume-extraction-demand
  partAiiiAttachmentA15 habitatQualityScoring true true false true

partBReferralBaselineDemand : VolumeExtractionDemand
partBReferralBaselineDemand = volume-extraction-demand
  partBReferralMaterial referralBaseline true false false true

------------------------------------------------------------------------
-- WrongType/source-diligence firewalls.
------------------------------------------------------------------------

data LibraryCatalogueEntryEqualsSubstantiveEcology : Set where
data FourVolumeSetExistenceEqualsContentsExtracted : Set where
data SaundersHavillLinkEqualsCurrentOnlineAvailability : Set where
data LegalDepositEqualsAgencyFinding : Set where

catalogueDoesNotProveSubstantiveEcology :
  LibraryCatalogueEntryEqualsSubstantiveEcology → ⊥
catalogueDoesNotProveSubstantiveEcology ()

setExistenceDoesNotMeanContentsExtracted :
  FourVolumeSetExistenceEqualsContentsExtracted → ⊥
setExistenceDoesNotMeanContentsExtracted ()

catalogueLinkDoesNotProveCurrentOnlineAvailability :
  SaundersHavillLinkEqualsCurrentOnlineAvailability → ⊥
catalogueLinkDoesNotProveCurrentOnlineAvailability ()

legalDepositDoesNotCreateAgencyFinding :
  LegalDepositEqualsAgencyFinding → ⊥
legalDepositDoesNotCreateAgencyFinding ()
