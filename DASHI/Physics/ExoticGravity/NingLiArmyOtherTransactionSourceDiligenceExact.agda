module DASHI.Physics.ExoticGravity.NingLiArmyOtherTransactionSourceDiligenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NING LI / AC GRAVITY / ARMY OTHER-TRANSACTION SOURCE DILIGENCE
--
-- The important correction is a custody-state refinement:
--   secondary transcriptions -> archived primary locator -> inspected carrier.
-- We have reached the middle state only.  The archive URL is now located and
-- independently corroborated as the FY2001 DoD report URL by the National
-- Academies, but this owner does not claim that the archived DOC bytes/page 66
-- have been inspected in this implementation session.
------------------------------------------------------------------------

record ArmyOtherTransactionSourceState : Set where
  constructor army-other-transaction-source-state
  field
    reportedAgreement : String
    reportedTitle : String
    reportedAwardingOffice : String
    reportedAwardee : String
    archivedPrimaryLocator : String
    independentReportExistenceCorroboration : String
    fy2001ReportLocatorRecovered : Bool
    primaryCarrierBytesInspected : Bool
    exactPage66RowVerifiedAgainstCarrier : Bool
    awardAmountPrimaryPaid : Bool
    scheduledDatesPrimaryPaid : Bool
    technicalObjectivePrimaryPaid : Bool
    armyTechnicalOutcomeUnknown : Bool
    nextReceipt : String

open ArmyOtherTransactionSourceState public

currentArmySourceState : ArmyOtherTransactionSourceState
currentArmySourceState = army-other-transaction-source-state
  "DAAH01-01-9-R001"
  "Gravito-Electro Magnetic Superconductivity Experiment"
  "reported: U.S. Army Aviation and Missile Command (AMCOM), AMSAM-AC-RD-BA"
  "reported: AC Gravity LLC"
  "https://web.archive.org/web/20210801183915id_/https://www.acq.osd.mil/dpap/Docs/FY01RPT.doc"
  "National Academies / NCBI Bookshelf independently cites www.acq.osd.mil/dpap/Docs/FY01RPT.doc as the FY2001 DoD Other Transactions report"
  true
  false
  false
  false
  false
  false
  true
  "materialise/inspect the archived FY01RPT.doc, verify page 66 row exactly, then acquire the underlying agreement/SOW and any closeout or test report"

secondaryTranscriptionDoesNotPayAwardRow : Bool
secondaryTranscriptionDoesNotPayAwardRow = true

archiveLocatorDoesNotEqualInspectedCarrier : Bool
archiveLocatorDoesNotEqualInspectedCarrier = true

armyTechnicalOutcomeUnknown : Bool
armyTechnicalOutcomeUnknown = true

record ArmySourcePromotionBoundary : Set where
  constructor army-source-promotion-boundary
  field
    archiveURLMayNominateCarrierAcquisition : Bool
    archiveURLAlonePaysRowText : Bool
    secondaryAgreementNumberMayGuideSearch : Bool
    noPublicCloseoutProvesClassification : Bool
    inspectedPrimaryRowRequiredForAwardPromotion : Bool
    inspectedCloseoutRequiredForOutcomePromotion : Bool

canonicalArmySourcePromotionBoundary : ArmySourcePromotionBoundary
canonicalArmySourcePromotionBoundary = army-source-promotion-boundary
  true false true false true true
