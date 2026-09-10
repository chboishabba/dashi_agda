module DASHI.Culture.AmyEskridgeMessageProvenanceBacktraceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Culture.AmyEskridgeOSINTSnowballExact as OSINT

------------------------------------------------------------------------
-- AMY ESKRIDGE MEMORIAL: REPORTED MESSAGE PROVENANCE BACKTRACE
--
-- The May-2022 message attributed to Amy is currently an OSINT discovery lead.
-- This owner formalises the reverse chain toward the nearest native carrier.
-- Each step may improve provenance without automatically authenticating the
-- message or proving any proposition about the manner of death.
------------------------------------------------------------------------

data BacktraceStage : Set where
  secondaryArticleStage : BacktraceStage
  originatingNewsReportStage : BacktraceStage
  publicMilburnPostStage : BacktraceStage
  screenshotCarrierStage : BacktraceStage
  nativeMessageExportStage : BacktraceStage
  deviceAccountMetadataStage : BacktraceStage

data StageStatus : Set where
  inspected : StageStatus
  referencedButNotInspected : StageStatus
  publicLeadLocated : StageStatus
  unresolved : StageStatus

record MessageBacktraceAtom : Set where
  constructor message-backtrace-atom
  field
    stage : BacktraceStage
    status : StageStatus
    locator : String
    relationToPrior : String
    exactCarrierIdentityPaid : Bool
    authorshipAuthenticationPaid : Bool
    timestampAuthenticationPaid : Bool
    chainOfCustodyPaid : Bool
    propositionSupportPaid : Bool

open MessageBacktraceAtom public

hindustanStage : MessageBacktraceAtom
hindustanStage = message-backtrace-atom
  secondaryArticleStage
  inspected
  "Hindustan Times, 23 April 2026, Amy Eskridge update"
  "reports that the Daily Mail published messages supplied by Franc Milburn"
  false false false false true

dailyMailStage : MessageBacktraceAtom
dailyMailStage = message-backtrace-atom
  originatingNewsReportStage
  referencedButNotInspected
  "Daily Mail report identified by Hindustan Times and subsequent reporting"
  "named upstream news source for the Milburn-supplied message screenshots; exact article carrier still to be inspected in this owner"
  false false false false false

milburnPublicPostStage : MessageBacktraceAtom
milburnPublicPostStage = message-backtrace-atom
  publicMilburnPostStage
  publicLeadLocated
  "Franc Milburn public X post dated 27 April 2026; downstream articles embed/reference post id media lead DTFArIwQuI"
  "closer-to-origin public posting by the person reported to have received the messages; exact post/media bytes still need direct archival capture"
  false false false false false

screenshotStage : MessageBacktraceAtom
screenshotStage = message-backtrace-atom
  screenshotCarrierStage
  unresolved
  "screenshots attributed to Franc Milburn circulation"
  "visual carrier may preserve message text/timestamps but requires image provenance, account identity and unedited-carrier checks"
  false false false false false

nativeMessageStage : MessageBacktraceAtom
nativeMessageStage = message-backtrace-atom
  nativeMessageExportStage
  unresolved
  "native Signal/SMS/DM/email export or equivalent"
  "preferred message-level carrier; not publicly authenticated in current OSINT review"
  false false false false false

metadataStage : MessageBacktraceAtom
metadataStage = message-backtrace-atom
  deviceAccountMetadataStage
  unresolved
  "account/device/timestamp metadata and provenance"
  "needed to bind a native message to Amy, recipient, date and unbroken provenance"
  false false false false false

messageLeadIsCurrentOSINTAtom :
  OSINT.proposition OSINT.reportedNonSuicideMessageLeadAtom ≡
    OSINT.reportedPreDeathNonSuicideStatement
messageLeadIsCurrentOSINTAtom = refl

record MessageBacktraceBoundary : Set where
  constructor message-backtrace-boundary
  field
    closerToOriginEqualsAuthenticated : Bool
    publicPostEqualsNativeMessageExport : Bool
    screenshotTextEqualsAuthorshipProof : Bool
    visibleTimestampEqualsMetadataAuthentication : Bool
    multipleArticlesEqualIndependentMessageCorroboration : Bool
    authenticatedPreDeathStatementDeterminesDeathManner : Bool
    backtraceMayRefineNextOSINTAcquisition : Bool

canonicalMessageBacktraceBoundary : MessageBacktraceBoundary
canonicalMessageBacktraceBoundary =
  message-backtrace-boundary false false false false false false true
