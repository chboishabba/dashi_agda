module DASHI.Culture.ScreenshotOpticsRadixBlackStoneAttributionExact where

-- Four user-supplied Instagram screenshots, received 2026-10-25.
-- THIS IS AN ATTRIBUTION / EVIDENCE-ROLE ATLAS, not a verification of
-- the screenshot's original reel, a flight-test report, or a new theology.
-- Claim attributions and canonical literary roots remain distinct.
-- Our toy detector lemma is imported from its existing canonical owner.

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Physics.Optics.DiffuserImagingObserverDynamicRangeExact as Imaging
import DASHI.Foundations.BaseTwelveCircleRepresentationBoundaryExact as Radix

------------------------------------------------------------------------
-- Screenshot accounts, reporting, and the older primary textual root.
-- The original Instagram reel URLs are not visible in the screenshots;
-- the handles cited below label COMMENT AUTHORS, not the reel producer.
------------------------------------------------------------------------

goesComment : Source.AttributedSource
goesComment =
  Source.mkNoDOISource
    "Instagram commenter evgenekb_"
    "Comment describing GOES-451M imaging on a purported Ka-52 display"
    "user-supplied screenshot 1000018617.png; 11w shown, not dated"
    "capture provided 2026-10-25"
    "conversation-upload:1000018617.png"
    (Source.namedSourceKind "social media comment screenshot")
    "firsthand-attributed description; no machine identity or performance certificate"
    Source.publicAttribution

radixCircleCaption : Source.AttributedSource
radixCircleCaption =
  Source.mkNoDOISource
    "Instagram account basetwelvegeometry"
    "Twelve-based Cartesian circle and discrete-pi assertions"
    "user-supplied screenshot 1000018618.png; 12 June shown, year unknown"
    "capture provided 2026-10-25"
    "conversation-upload:1000018618.png"
    (Source.namedSourceKind "social media geometry assertion")
    "source claim only; exact value of pi is not modified by radix"
    Source.publicAttribution

radixReply : Source.AttributedSource
radixReply =
  Source.mkNoDOISource
    "Instagram account basetwelvegeometry, replying to sphinyzw"
    "No-repeating-decimals and circle-in-twelfths reply"
    "user-supplied screenshot 1000018619.png"
    "capture provided 2026-10-25"
    "conversation-upload:1000018619.png"
    (Source.namedSourceKind "social media discussion screenshot")
    "preserves author/commenter contrast: sphinyzw raised notation objection"
    Source.publicAttribution

stoneComment : Source.AttributedSource
stoneComment =
  Source.mkNoDOISource
    "Unidentified commenter in screenshot"
    "Black Stone, tawaf and attributed statement of Umar"
    "user-supplied screenshot 1000018620.png; commenter handle not visible"
    "capture provided 2026-10-25"
    "conversation-upload:1000018620.png"
    (Source.namedSourceKind "unattributed social media comment")
    "religious interpretation; no attribution to an unknown account"
    Source.publicAttribution

goesSecondaryReport : Source.AttributedSource
goesSecondaryReport =
  Source.mkNoDOISource
    "Piotr Butowski / The War Zone"
    "Enhanced Version Of Russia's Ka-52 Attack Helicopter Appears"
    "defence reporting, 21 July 2023"
    "2023"
    "https://www.twz.com/enhanced-version-of-russias-ka-52-attack-helicopter-appears"
    Source.newsSource
    "secondary identification of GOES-451M on Ka-52M, not calibrated image-quality testing"
    Source.publicAttribution

bukhari1597 : Source.AttributedSource
bukhari1597 =
  Source.mkNoDOISource
    "al-Bukhari (compiler); report ascribed to Umar via Abis ibn Rabia"
    "Sahih al-Bukhari, Book of Hajj, hadith 1597"
    "classical transmitted textual tradition; modern online edition"
    "ninth century CE compilation"
    "https://sunnah.com/bukhari:1597"
    (Source.namedSourceKind "classical Islamic hadith collection")
    "original collection root for the attributed statement; not eyewitness material assay or proof of divinity"
    Source.publicAttribution

blackStoneMaterialsStudy : Source.AttributedSource
blackStoneMaterialsStudy =
  Source.mkNoDOISource
    "Kerim Kocak"
    "Features of the Hajar al-Aswad, Black Stone of Makkah, Saudi Arabia"
    "Konya Journal of Engineering Sciences 11(3); 2023"
    "2023"
    "https://dergipark.org.tr/en/pub/konjes/article/1244222"
    Source.academicArticleSource
    "published geological discussion; conclusions and sample identity require independent scrutiny"
    Source.publicAttribution

screenshotAtlas : Source.AttributedSourceAtlas
screenshotAtlas =
  Source.mkSourceAtlas
    "2026-10-25 optics/radix/Black Stone claim atlas"
    "DASHI.Culture.ScreenshotOpticsRadixBlackStoneAttributionExact"
    (goesComment ∷ radixCircleCaption ∷ radixReply ∷
     stoneComment ∷ goesSecondaryReport ∷ bukhari1597 ∷
     blackStoneMaterialsStudy ∷ [])
    "screen captures, reported hardware identity, mathematical critique, classical-text attribution, and materials inquiry; all stages separate"

sevenDistinctAtlasEntries :
  Source.sourceCount (Source.sources screenshotAtlas) ≡ 7
sevenDistinctAtlasEntries = refl

atlasPromotesNoDomainAuthority :
  (validation : String) →
  Source.atlasCreatesAuthority screenshotAtlas ≡ false
atlasPromotesNoDomainAuthority validation =
  Source.atlasCreatesAuthorityIsFalse screenshotAtlas

------------------------------------------------------------------------
-- Evidence roles: a hadith report is not an independent physical assay;
-- a social-media claim is not a calibrated sensor measurement.
------------------------------------------------------------------------

data EvidenceRole : Set where
  screenshotAssertion : EvidenceRole
  independentPublicReporting : EvidenceRole
  classicalTextWitness : EvidenceRole
  scientificPhysicalAssay : EvidenceRole
  calibratedSensorTest : EvidenceRole

screenshotIsNotCalibration :
  screenshotAssertion ≡ calibratedSensorTest → ⊥
screenshotIsNotCalibration ()

traditionIsNotPhysicalAssay :
  classicalTextWitness ≡ scientificPhysicalAssay → ⊥
traditionIsNotPhysicalAssay ()

data NoiselessGOES451MCertificateFromTheseScreenshots : Set where

noNoiselessCertificateFromTheseScreenshots :
  NoiselessGOES451MCertificateFromTheseScreenshots → ⊥
noNoiselessCertificateFromTheseScreenshots ()

-- Exact preexisting toy result: a scalar clipping collision survives
-- arbitrary postprocessing.  It is NOT a numerical GOES-451M calibration.
opticalPostprocessingDoesNotRecoverAClippedDifference :
  {Output : Set} →
  (post : Nat → Output) →
  post (Imaging.clipAtOne Imaging.one)
    ≡ post (Imaging.clipAtOne Imaging.two)
opticalPostprocessingDoesNotRecoverAClippedDifference =
  Imaging.postprocessingDoesNotRepairClip

record ThreeSubjectBoundary : Set where
  constructor threeSubjectBoundary
  field
    opticsCalibratedByCapture : Bool
    opticsCalibratedByCaptureIsFalse : opticsCalibratedByCapture ≡ false
    piRedefinedByTwelfths : Bool
    piRedefinedByTwelfthsIsFalse : piRedefinedByTwelfths ≡ false
    religiousReportPromotedAsPhysicalEvidence : Bool
    religiousReportPromotedAsPhysicalEvidenceIsFalse :
      religiousReportPromotedAsPhysicalEvidence ≡ false

canonicalThreeSubjectBoundary : ThreeSubjectBoundary
canonicalThreeSubjectBoundary =
  threeSubjectBoundary false refl false refl false refl

-- Reuse, not identification: the finite radix/ratio lemma is already owned
-- by the foundation module and imported explicitly.
sameHalfAcrossRadices :
  Radix._≈_ Radix.baseTenHalf Radix.baseTwelveHalf
sameHalfAcrossRadices = Radix.sameHalfAcrossRadices
