module DASHI.Law.SensibLawWoogarooEPBC8575PortalClockManifestationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- EPBC 2019/8575 PORTAL MANIFESTATIONS / PRELIMINARY-DOCUMENTATION CLOCK
--
-- Keep three different objects separate:
--   (1) mutable portal status manifestations;
--   (2) the statutory s 95B -> s 130 clock;
--   (3) the literal Part 9 decision/approval instrument.
--
-- A portal label can route acquisition but cannot create legal effect.
-- A community process summary can locate the statutory mechanism but cannot
-- substitute for the Act, the Minister's receipt date, an extension notice or
-- the eventual Part 9 instrument.
------------------------------------------------------------------------

epbcAct95B130Source : Source.AttributedSource
epbcAct95B130Source = Source.mkNoDOISource
  "Commonwealth of Australia"
  "Environment Protection and Biodiversity Conservation Act 1999 — sections 95B and 130"
  "Federal Register of Legislation"
  "2026"
  "https://www.legislation.gov.au/C2004A00485/2026-07-01"
  Source.governmentSource
  "Primary statutory source for the post-comment preliminary-documentation procedure and the Part 9 decision clock. It does not itself pay the project-specific Minister-receipt date, extension notice or approval outcome."
  Source.publicAttribution

epbcPortal8575ManifestationSource : Source.AttributedSource
epbcPortal8575ManifestationSource = Source.mkNoDOISource
  "Australian Government / National Environmental Protection Agency"
  "Springfield Residential Development — EPBC 2019/8575 — project decision surface"
  "EPBC Act Public Portal"
  "2026"
  "https://epbcpublicportal.environment.gov.au/all-notices/project-decision/?id=3c8edc14-9ffb-ee11-9f89-00224892a860"
  Source.governmentSource
  "Primary portal manifestation for project identity and displayed workflow/status fields. The portal itself warns that project/status fields are being updated; a displayed status string is not the Part 9 instrument and is retained as a time-bound manifestation rather than timeless legal state."
  Source.publicAttribution

saveWoogarooProcessSummary : Source.AttributedSource
saveWoogarooProcessSummary = Source.mkNoDOISource
  "Save Woogaroo Forest"
  "EPBC Submissions — Springview Village 2 & 3 process FAQ"
  "Save Woogaroo Forest"
  "2026"
  "https://savewoogarooforest.com.au/epbc-submissions"
  Source.communitySource
  "Community/advocacy process summary stating that the proponent manages the s 95A(3) comment process, describing a 40-business-day decision period after final documentation/administrative requirements, and reporting more than 850 submissions that the group could account for. It is a secondary locator and bounded community count; the Act and official project records remain the primary payment surfaces."
  Source.publicAttribution

------------------------------------------------------------------------
-- Mutable portal manifestations.
------------------------------------------------------------------------

data PortalDecisionStatus : Set where
  decisionStatusExpired : PortalDecisionStatus
  decisionStatusPublished : PortalDecisionStatus
  decisionStatusOther : PortalDecisionStatus

record PortalManifestation : Set where
  constructor portal-manifestation
  field
    source : Source.AttributedSource
    projectStatus : String
    decisionStatus : PortalDecisionStatus
    observationBounded : Bool
    importsPart9LegalEffect : Bool

open PortalManifestation public

expiredPortalManifestation : PortalManifestation
expiredPortalManifestation = portal-manifestation
  epbcPortal8575ManifestationSource
  "Final Preliminary Documentation Published"
  decisionStatusExpired
  true
  false

publishedPortalManifestation : PortalManifestation
publishedPortalManifestation = portal-manifestation
  epbcPortal8575ManifestationSource
  "Final Preliminary Documentation Published"
  decisionStatusPublished
  true
  false

finalPDPublicationStatusPaid : Bool
finalPDPublicationStatusPaid = true

------------------------------------------------------------------------
-- Portal status cannot recover operative Part 9 legal state.
------------------------------------------------------------------------

data PortalWorld : Set where
  expiredWithoutPart9Instrument : PortalWorld
  expiredWithLaterPart9Instrument : PortalWorld

data OperativePart9State : Set where
  noOperativePart9Instrument : OperativePart9State
  operativePart9Instrument : OperativePart9State

portalStatusObserver : PortalWorld → PortalDecisionStatus
portalStatusObserver expiredWithoutPart9Instrument = decisionStatusExpired
portalStatusObserver expiredWithLaterPart9Instrument = decisionStatusExpired

operativePart9Query : PortalWorld → OperativePart9State
operativePart9Query expiredWithoutPart9Instrument = noOperativePart9Instrument
operativePart9Query expiredWithLaterPart9Instrument = operativePart9Instrument

operativePart9Differs :
  operativePart9Query expiredWithoutPart9Instrument ≡
  operativePart9Query expiredWithLaterPart9Instrument → ⊥
operativePart9Differs ()

portalStatusDoesNotPayOperativeLegalState :
  INF.FactorsThrough portalStatusObserver operativePart9Query → ⊥
portalStatusDoesNotPayOperativeLegalState =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      expiredWithoutPart9Instrument
      expiredWithLaterPart9Instrument
      refl
      operativePart9Differs)

------------------------------------------------------------------------
-- Statutory clock receipts.
------------------------------------------------------------------------

data ClockCoordinate : Set where
  finalDocumentPreparedAfterComments : ClockCoordinate
  documentsGivenToMinister : ClockCoordinate
  requiredFeePaid : ClockCoordinate
  finalDocumentPublished : ClockCoordinate
  fortyBusinessDayDecisionPeriod : ClockCoordinate
  writtenLongerPeriod : ClockCoordinate

record ClockReceipt : Set where
  constructor clock-receipt
  field
    coordinate : ClockCoordinate
    source : Source.AttributedSource
    exactRule : String
    primaryTextPaid : Bool
    projectSpecificDatePaid : Bool

open ClockReceipt public

section95BReceiptStartsClock : ClockReceipt
section95BReceiptStartsClock = clock-receipt
  documentsGivenToMinister
  epbcAct95B130Source
  "For assessment on preliminary documentation where comments were received, s 95B(1) requires the designated proponent to prepare the final document and give the Minister that document plus the comments; s 130(1B) measures the relevant decision period from the Minister's receipt of the s 95B material."
  true
  false

requiredFeePaymentPartOfReceiptGate : ClockReceipt
requiredFeePaymentPartOfReceiptGate = clock-receipt
  requiredFeePaid
  epbcAct95B130Source
  "Section 95B(1A) provides that the designated proponent is taken not to have given the Minister the s 95B(1) documents if a required fee has not been paid."
  true
  false

section130FortyBusinessDayClock : ClockReceipt
section130FortyBusinessDayClock = clock-receipt
  fortyBusinessDayDecisionPeriod
  epbcAct95B130Source
  "For an action assessed on preliminary documentation, s 130 provides a 40-business-day relevant period beginning on the first business day after the Minister receives the documents under s 95B(1) or the statement under s 95B(3), subject to the Act's timing provisions."
  true
  false

section130WrittenExtensionMayLengthenPeriod : ClockReceipt
section130WrittenExtensionMayLengthenPeriod = clock-receipt
  writtenLongerPeriod
  epbcAct95B130Source
  "Section 130 permits the Minister to specify in writing a longer period than the ordinary relevant period. The existence and content of the project-specific extension notice are separate evidence objects."
  true
  false

minister95BReceiptDateOpen : ClockReceipt
minister95BReceiptDateOpen = clock-receipt
  documentsGivenToMinister
  epbcAct95B130Source
  "Exact project-specific date on which the Minister received the EPBC 2019/8575 s 95B material; not paid by portal publication status alone."
  true
  false

------------------------------------------------------------------------
-- WrongType / no-skip firewalls.
------------------------------------------------------------------------

data FinalPDPublicationStartsClockByItself : Set where
data ExpiredStatusImpliesSupersedingReferral : Set where
data PublishedStatusEqualsPart9Approval : Set where
data CommunityCountEqualsOfficialSubmissionCount : Set where
\data CommunityFAQPaysMinisterReceiptDate : Set where

finalPDPublicationDoesNotStartClockByItself :
  FinalPDPublicationStartsClockByItself → ⊥
finalPDPublicationDoesNotStartClockByItself ()

decisionStatusExpiredDoesNotImplySupersedingReferral :
  ExpiredStatusImpliesSupersedingReferral → ⊥
decisionStatusExpiredDoesNotImplySupersedingReferral ()

decisionStatusPublishedDoesNotEqualPart9Approval :
  PublishedStatusEqualsPart9Approval → ⊥
decisionStatusPublishedDoesNotEqualPart9Approval ()

communityCountDoesNotEqualOfficialSubmissionCount :
  CommunityCountEqualsOfficialSubmissionCount → ⊥
communityCountDoesNotEqualOfficialSubmissionCount ()

communityFAQDoesNotPayMinisterReceiptDate :
  CommunityFAQPaysMinisterReceiptDate → ⊥
communityFAQDoesNotPayMinisterReceiptDate ()

------------------------------------------------------------------------
-- Submission-count provenance.
------------------------------------------------------------------------

record SubmissionCountReceipt : Set where
  constructor submission-count-receipt
  field
    source : Source.AttributedSource
    boundedStatement : String
    exactOfficialTotalPaid : Bool

open SubmissionCountReceipt public

moreThan850IsCommunityAccountedCountOnly : SubmissionCountReceipt
moreThan850IsCommunityAccountedCountOnly = submission-count-receipt
  saveWoogarooProcessSummary
  "Save Woogaroo Forest reports more than 850 Springview Village 2 & 3 submissions that the group could account for. This is not promoted into an exact official total."
  false

exactSubmissionCountRemainsOpen : SubmissionCountReceipt
exactSubmissionCountRemainsOpen = submission-count-receipt
  saveWoogarooProcessSummary
  "Exact official total of comments received under the EPBC 2019/8575 public-comment process remains an acquisition residual until paid by an authoritative project record."
  false

------------------------------------------------------------------------
-- Current Pareto.
------------------------------------------------------------------------

record PortalClockPareto : Set where
  constructor portal-clock-pareto
  field
    literalPart9InstrumentBeforePortalConclusion : Bool
    minister95BReceiptBeforeIndependentClockReconstruction : Bool
    projectSpecificWrittenExtensionCanControlPracticalDeadline : Bool
    portalManifestationsRetainedAppendOnly : Bool
    communitySourceMayLocatePrimary : Bool
    communitySourceMayPayPrimary : Bool
    exactOfficialSubmissionCountOpen : Bool

canonicalPortalClockPareto : PortalClockPareto
canonicalPortalClockPareto = portal-clock-pareto
  true true true true true false true
