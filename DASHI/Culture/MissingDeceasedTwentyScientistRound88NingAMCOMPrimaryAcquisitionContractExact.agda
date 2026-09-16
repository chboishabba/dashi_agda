module DASHI.Culture.MissingDeceasedTwentyScientistRound88NingAMCOMPrimaryAcquisitionContractExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- ROUND 88 / NING LI AMCOM PRIMARY ACQUISITION CONTRACT
--
-- Public web search is saturated with derivative transcriptions of the FY2001
-- DoD Other Transactions report.  The archived legacy .doc remains a known
-- primary locator, but direct byte acquisition through the current tool
-- environment failed.  That is a tool/access limitation, not evidence that
-- the source does not exist or that Army records are unavailable in principle.
--
-- AMCOM's current FOIA page gives a direct Army producer route through the
-- CIO/G6 FOIA office at Redstone Arsenal.  The next acquisition demand is
-- therefore exact-record-class scoped: agreement instrument, SOW/attachments,
-- modifications, payment/disbursement records, administrative closeout, and
-- final technical/result records for DAAH01-01-9-R001.
------------------------------------------------------------------------

record PrimaryAcquisitionRoute : Set where
  constructor primaryAcquisitionRoute
  field
    agreementNumber : String
    agreementTitle : String
    awardingOffice : String
    currentProducer : String
    routeReference : String
    exactRecordClasses : String
    willingnessToPayRequired : Bool

canonicalAMCOMRoute : PrimaryAcquisitionRoute
canonicalAMCOMRoute = primaryAcquisitionRoute
  "DAAH01-01-9-R001"
  "Gravito - Electro Magnetic Superconductivity Experiment"
  "US Army Aviation and Missile Command (AMCOM), AMSAM-AC-RD-BA"
  "AMCOM CIO/G6 FOIA Office, Redstone Arsenal"
  "https://www.amcom.army.mil/FOIA/"
  "agreement instrument; statement of work and attachments; modifications; obligation/disbursement/payment records; administrative closeout; final technical/result records"
  true

amcomCurrentFOIARoutePaid : Bool
amcomCurrentFOIARoutePaid = true

exactRecordClassRequestRequired : Bool
exactRecordClassRequestRequired = true

historicalAwardOfficeCoordinatePaid : Bool
historicalAwardOfficeCoordinatePaid = true

waybackPrimaryLocatorPaid : Bool
waybackPrimaryLocatorPaid = true

waybackByteAcquisitionAttempted : Bool
waybackByteAcquisitionAttempted = true

waybackPrimaryBytesAcquired : Bool
waybackPrimaryBytesAcquired = false

toolAccessFailureDoesNotPaySourceAbsence : Bool
toolAccessFailureDoesNotPaySourceAbsence = true

toolAccessFailureDoesNotPayRecordNonexistence : Bool
toolAccessFailureDoesNotPayRecordNonexistence = true

toolAccessFailureDoesNotPayClassification : Bool
toolAccessFailureDoesNotPayClassification = true

archivedReportBytesStillDesired : Bool
archivedReportBytesStillDesired = true

primaryAgreementInstrumentStillUnacquired : Bool
primaryAgreementInstrumentStillUnacquired = true

paymentDisbursementStillUnresolved : Bool
paymentDisbursementStillUnresolved = true

administrativeCloseoutStillUnresolved : Bool
administrativeCloseoutStillUnresolved = true

technicalOutcomeStillUnresolved : Bool
technicalOutcomeStillUnresolved = true

classificationDispositionStillUnresolved : Bool
classificationDispositionStillUnresolved = true

foiaLogArchaeologyNowDominated : Bool
foiaLogArchaeologyNowDominated = true

h2Paid : Bool
h2Paid = false

h3Paid : Bool
h3Paid = false

record NingAMCOMAcquisitionBoundary : Set where
  constructor ningAMCOMAcquisitionBoundary
  field
    routePaid : Bool
    routePaidIsTrue : routePaid ≡ true
    byteCustodyPaid : Bool
    byteCustodyPaidIsFalse : byteCustodyPaid ≡ false
    toolFailureNotAbsence : Bool
    toolFailureNotAbsenceIsTrue : toolFailureNotAbsence ≡ true
    outcomeUnresolved : Bool
    outcomeUnresolvedIsTrue : outcomeUnresolved ≡ true

canonicalNingAMCOMAcquisitionBoundary : NingAMCOMAcquisitionBoundary
canonicalNingAMCOMAcquisitionBoundary =
  ningAMCOMAcquisitionBoundary true refl false refl true refl true refl
