module DASHI.Culture.PowersPlantationParadiseSourceAcquisitionPromotionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.PowersPlantationParadiseArchiveModalityExact as Modality
import DASHI.Culture.PowersPlantationParadiseEvidenceGraphExact as Graph
import DASHI.Culture.PowersPlantationParadiseInvestigationParetoExact as Routing

------------------------------------------------------------------------
-- HISTORICAL SOURCE ACQUISITION / PROMOTION GATE
--
-- Design inspiration from current repository-intelligence / verification work
-- is kept at design-precedent level.  This owner is a Powers-specific historical
-- adapter over already-merged provenance/non-factorability/selective-reopening
-- machinery; it does not import unmerged sibling PRs as theorem authority.
------------------------------------------------------------------------

data ResolutionStage : Set where
  secondaryCoordinateOnly : ResolutionStage
  locatedManifestation : ResolutionStage
  materializedManifestation : ResolutionStage
  directlyInspectedManifestation : ResolutionStage
  transcribedManifestation : ResolutionStage
  sameItemBoundManifestation : ResolutionStage
  claimQualifiedManifestation : ResolutionStage

record HistoricalSourceAcquisitionReceipt : Set where
  constructor historical-source-acquisition-receipt
  field
    manifestationReference : String
    sourceGenre : Modality.SourceGenre
    stage : ResolutionStage
    sourceAuthorityReference : String
    sameItemBindingReference : String
    directlyInspected : Bool
    claimQualified : Bool
    createsHistoricalTruth : Bool
    createsHistoricalTruthIsFalse : createsHistoricalTruth ≡ false
    createsCausalEffect : Bool
    createsCausalEffectIsFalse : createsCausalEffect ≡ false

open HistoricalSourceAcquisitionReceipt public

record HistoricalSourceAcquisitionObligation : Set where
  constructor historical-source-acquisition-obligation
  field
    targetReference : String
    requiredStage : ResolutionStage
    acquisitionReasonReference : String
    dependentConsumerReference : String
    routeReference : String
    currentlyPaid : Bool
    currentlyPaidIsFalse : currentlyPaid ≡ false

open HistoricalSourceAcquisitionObligation public

------------------------------------------------------------------------
-- Existing source coordinates: bounded to what has actually been inspected.
------------------------------------------------------------------------

julien1781SecondaryCoordinateReceipt : HistoricalSourceAcquisitionReceipt
julien1781SecondaryCoordinateReceipt =
  historical-source-acquisition-receipt
    "Affiches américaines, 13 November 1781, Julien sale/theatre notice"
    Modality.runawaySaleAdvertisement
    secondaryCoordinateOnly
    "coordinate preserved in later scholarship / Laméca; primary image not directly inspected in this branch"
    "same-record contribution × coercive-status join retained by EnslavedDistributionEvidence owner"
    false
    false
    false refl
    false refl

minette1784WillSecondaryCoordinateReceipt : HistoricalSourceAcquisitionReceipt
minette1784WillSecondaryCoordinateReceipt =
  historical-source-acquisition-receipt
    "ANOM, DPPC, Notaire Michel, minutes of 9 June 1784, Testament du Sr Saint-Martin"
    Modality.notarialWill
    secondaryCoordinateOnly
    "primary coordinate supplied through Prest 2019; exact primary manifestation not directly inspected in this branch"
    "same Minette contract/nonpayment object retained by MinetteMicrohistory owner"
    false
    false
    false refl
    false refl

lise1786AnnouncementSecondaryCoordinateReceipt : HistoricalSourceAcquisitionReceipt
lise1786AnnouncementSecondaryCoordinateReceipt =
  historical-source-acquisition-receipt
    "Affiches américaines, 28 January 1786, Lise/Saint-Marc announcement"
    Modality.theatreAnnouncement
    secondaryCoordinateOnly
    "event coordinate retained through later scholarly reconstruction; exact issue image not directly inspected in this branch"
    "same Lise Saint-Marc event retained by PerformerComparison owner"
    false
    false
    false refl
    false refl

------------------------------------------------------------------------
-- Live acquisition obligations.
------------------------------------------------------------------------

july1790PrimaryIssueObligation : HistoricalSourceAcquisitionObligation
july1790PrimaryIssueObligation =
  historical-source-acquisition-obligation
    "underlying Affiches américaines manifestation for the disputed July 1790 Minette/Périgord notice"
    directlyInspectedManifestation
    "discriminate Prest 1 July / Laméca 17 July / multiple-notice possibilities"
    "Minette chronology contestation + performance-event ledger"
    "powers:primary-corpus-saturation"
    false refl

minetteSettlementObligation : HistoricalSourceAcquisitionObligation
minetteSettlementObligation =
  historical-source-acquisition-obligation
    "Saint-Martin estate/executor account or equivalent same-object settlement record"
    sameItemBoundManifestation
    "distinguish contracted arrears/intended disposition from actual transfer/final settlement"
    "Minette compensation dossier + actor distribution benefit coordinate"
    "powers:minette-compensation-settlement"
    false refl

saintDomingueSeatingRuleObligation : HistoricalSourceAcquisitionObligation
saintDomingueSeatingRuleObligation =
  historical-source-acquisition-obligation
    "applicable Saint-Domingue theatre/police ordinance, price schedule or enforcement record"
    directlyInspectedManifestation
    "discriminate formal-rule, architecture/custom and realised-practice hypotheses"
    "rules × architecture × practice atlas"
    "powers:saint-domingue-seating-rule"
    false refl

------------------------------------------------------------------------
-- Location / inspection / qualification are independent promotion stages.
------------------------------------------------------------------------

data LocationInspectionState : Set where
  locatedUninspected : LocationInspectionState
  locatedInspected : LocationInspectionState

data LocationReading : Set where sourceLocated : LocationReading

data InspectionReading : Set where notDirectlyInspected directlyInspectedReading : InspectionReading

locationReading : LocationInspectionState → LocationReading
locationReading _ = sourceLocated

inspectionReading : LocationInspectionState → InspectionReading
inspectionReading locatedUninspected = notDirectlyInspected
inspectionReading locatedInspected = directlyInspectedReading

inspectionReadingDiffers :
  inspectionReading locatedUninspected ≡ inspectionReading locatedInspected → ⊥
inspectionReadingDiffers ()

locationCannotRecoverInspection :
  INF.FactorsThrough locationReading inspectionReading → ⊥
locationCannotRecoverInspection =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      locatedUninspected
      locatedInspected
      refl
      inspectionReadingDiffers)

data InspectionQualificationState : Set where
  inspectedUnqualified : InspectionQualificationState
  inspectedQualified : InspectionQualificationState

data InspectionSurface : Set where inspectedSurface : InspectionSurface

data QualificationReading : Set where qualificationOpen qualificationPaid : QualificationReading

inspectionSurface : InspectionQualificationState → InspectionSurface
inspectionSurface _ = inspectedSurface

qualificationReading : InspectionQualificationState → QualificationReading
qualificationReading inspectedUnqualified = qualificationOpen
qualificationReading inspectedQualified = qualificationPaid

qualificationReadingDiffers :
  qualificationReading inspectedUnqualified ≡ qualificationReading inspectedQualified → ⊥
qualificationReadingDiffers ()

inspectionCannotRecoverQualification :
  INF.FactorsThrough inspectionSurface qualificationReading → ⊥
inspectionCannotRecoverQualification =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      inspectedUnqualified
      inspectedQualified
      refl
      qualificationReadingDiffers)

------------------------------------------------------------------------
-- Once the primary issue is actually acquired, the already-canonical selective
-- reopening graph determines what may reopen; acquisition itself pays neither
-- chronology nor event truth.
------------------------------------------------------------------------

julyChronologyReopeningAnchor : Routing.PrimaryIssueChronologyReopening
julyChronologyReopeningAnchor = Routing.primaryIssueReopensChronology

julyEventLedgerReopeningAnchor : Routing.PrimaryIssueEventLedgerReopening
julyEventLedgerReopeningAnchor = Routing.primaryIssueReopensEventLedger

record PowersSourceAcquisitionPromotionBoundary : Set where
  constructor powers-source-acquisition-promotion-boundary
  field
    locatedManifestationImpliesDirectInspection : Bool
    locatedManifestationImpliesDirectInspectionIsFalse :
      locatedManifestationImpliesDirectInspection ≡ false
    directInspectionImpliesClaimQualification : Bool
    directInspectionImpliesClaimQualificationIsFalse :
      directInspectionImpliesClaimQualification ≡ false
    transcriptionImpliesHistoricalTruth : Bool
    transcriptionImpliesHistoricalTruthIsFalse :
      transcriptionImpliesHistoricalTruth ≡ false
    exactItemBindingImpliesCausalEffect : Bool
    exactItemBindingImpliesCausalEffectIsFalse :
      exactItemBindingImpliesCausalEffect ≡ false
    secondaryCoordinateMayRemainUsefulAcquisitionLead : Bool
    secondaryCoordinateMayRemainUsefulAcquisitionLeadIsTrue :
      secondaryCoordinateMayRemainUsefulAcquisitionLead ≡ true
    acquisitionReopensOnlyDeclaredConsumers : Bool
    acquisitionReopensOnlyDeclaredConsumersIsTrue :
      acquisitionReopensOnlyDeclaredConsumers ≡ true
    currentPrimaryCoordinatesAreNotSilentlyPromotedToDirectInspection : Bool
    currentPrimaryCoordinatesAreNotSilentlyPromotedToDirectInspectionIsTrue :
      currentPrimaryCoordinatesAreNotSilentlyPromotedToDirectInspection ≡ true

canonicalPowersSourceAcquisitionPromotionBoundary :
  PowersSourceAcquisitionPromotionBoundary
canonicalPowersSourceAcquisitionPromotionBoundary =
  powers-source-acquisition-promotion-boundary
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
