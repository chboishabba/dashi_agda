module DASHI.Culture.MissingDeceasedTwentyScientistRound30AmyArchivedStatementAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- ROUND 30: AMY ARCHIVED-STATEMENT ACQUISITION
--
-- Search resolves an exact archived social-post locator for the September 2020
-- statement previously carried only through later reproductions.  The capture
-- is still an associate-posted screenshot attributed to Amy, not an
-- authenticated Amy-origin message.  It pays source location and preservation,
-- not paper identity, NASA-review transaction identity, or same-object semantics.
------------------------------------------------------------------------

record ArchivedStatementAcquisition : Set where
  constructor archived-statement-acquisition
  field
    source : Attribution.AttributedSource
    archivedPostLocatorPaid : Bool
    captureTimestampPaid : Bool
    associatePostedScreenshotPaid : Bool
    statementAttributionToAmyPaid : Bool
    authenticatedAmyOriginalPaid : Bool
    paperIdentifierPaid : Bool
    nasaReviewReceiptPaid : Bool
    ceaseAndDesistRecordPaid : Bool
    sameObjectSemanticsPaid : Bool
    pays : String
    doesNotPay : String
    nextLiteralPayment : String

open ArchivedStatementAcquisition public

amyArchivedPostSource : Attribution.AttributedSource
amyArchivedPostSource = Attribution.mkNoDOISource
  "Alien Scientist social post preserving screenshot attributed to Amy Eskridge"
  "Archived September 18, 2020 post containing the NASA-review statement screenshot"
  "Internet Archive capture of Twitter/X post 1306981668419301379"
  "2020"
  "https://web.archive.org/web/20200918154520id_/https://twitter.com/Alien_Scientist/status/1306981668419301379"
  Attribution.archivalSource
  "captured-source locator for the associate-posted screenshot attributed to Amy; retained as attribution-bearing self-report rather than an authenticated Amy-origin primary message"
  Attribution.publicAttribution

amyArchivedPostSnowball : Snowball.SourceRoleSnowballReceipt amyArchivedPostSource
amyArchivedPostSnowball = Snowball.canonicalSourceRoleSnowballReceipt amyArchivedPostSource

amyArchivedStatement : ArchivedStatementAcquisition
amyArchivedStatement = archived-statement-acquisition
  amyArchivedPostSource
  true
  true
  true
  true
  false
  false
  false
  false
  false
  "exact archived locator and capture time for the associate-posted screenshot; the screenshot attributes to Amy an unnamed NASA-MSFC team-member work lineage and an unnamed paper said to be under NASA review"
  "authentication of the original Amy message, report title/number, author list, NASA review case/receipt, cease-and-desist record, identity with TM 20205010911, H2, H3, suppression, or causal linkage"
  "recover the original message/email or independent NASA review/IP-release metadata carrying an identity-bearing key such as title, author, report number, SAA number, POAMS/V3 name or review case identifier"

archivedPostLocatorPaid : Bool
archivedPostLocatorPaid = true

captureTimestampPaid : Bool
captureTimestampPaid = true

associatePostedScreenshotPaid : Bool
associatePostedScreenshotPaid = true

authenticatedAmyOriginalPaid : Bool
authenticatedAmyOriginalPaid = false

paperIdentifierPaid : Bool
paperIdentifierPaid = false

nasaReviewReceiptPaid : Bool
nasaReviewReceiptPaid = false

sameObjectSemanticsPaid : Bool
sameObjectSemanticsPaid = false

archiveCaptureDoesNotAuthenticateUnderlyingSpeaker : Bool
archiveCaptureDoesNotAuthenticateUnderlyingSpeaker = true

quotedSelfReportDoesNotCreateNASAReceipt : Bool
quotedSelfReportDoesNotCreateNASAReceipt = true

round30H2PaidCount : Nat
round30H2PaidCount = 0

round30H3PaidCount : Nat
round30H3PaidCount = 0

round30Pareto : String
round30Pareto = "The September-2020 statement now has an exact archived-post locator and capture timestamp, so generic source-location debt is paid. The remaining high-alpha debt is identity-bearing: recover Amy's original email/message or a NASA IP/release-review record that names the paper, author, report number, SAA8-1519855, POAMS/V3 or another literal same-object key. Archive preservation alone cannot identify TM 20205010911."