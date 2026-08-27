module DASHI.Foundations.WettePrimaryTextAcquisitionPlanExact where

------------------------------------------------------------------------
-- WETTE PRIMARY-TEXT ACQUISITION PLAN
--
-- Source-attributed acquisition targets for the three late Wette items most
-- relevant to theorem discharge.  This module records where the text should be
-- obtained without promoting bibliographic location into primary-text recovery.
--
-- JSL 1974b:
--   Eduard Wette, "A Canonical System for the Operative Translation of
--   Formalized Number Theory as a Tool for the Refutation of Arithmetic
--   (Abstract)", Journal of Symbolic Logic 39 (1974), 387--388.
--   Retrieval routes: JSL issue/meeting-report backfile via JSTOR or Cambridge
--   Core.  No DOI is asserted here until the primary journal record is checked.
--
-- JSL 1976:
--   Eduard Wette, "A Simplifying Complication Concerning My
--   Inconsistency-Deduction within Formalized Arithmetic (Abstract)", Journal
--   of Symbolic Logic 41 (1976), 272--273.
--   Retrieval routes: JSL issue/meeting-report backfile via JSTOR or Cambridge
--   Core.  No DOI is asserted here until the primary journal record is checked.
--
-- International Logic Review 1974a:
--   Eduard Wette, "Contradiction within Pure Number Theory because of a
--   System-Internal 'Consistency'-Deduction", International Logic Review 9
--   (1974), 51--62.
--   Retrieval route: interlibrary document delivery / physical holdings located
--   through WorldCat, SBN or comparable national/research-library catalogues.
--   No verified DOI is known and none is fabricated.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.SourceAcquisitionGeometryExact as Acquisition
import DASHI.Foundations.WetteHistoricalSourceAtlasExact as Source

------------------------------------------------------------------------
-- Primary acquisition targets.
------------------------------------------------------------------------

wette1974CanonicalSystemAcquisition : Acquisition.SourceAcquisitionTarget
wette1974CanonicalSystemAcquisition =
  Acquisition.sourceAcquisitionTarget
    "Wette 1974b, Journal of Symbolic Logic 39"
    "pp. 387--388; Association for Symbolic Logic meeting-report abstract"
    Acquisition.commercialBackfile
    Acquisition.publisherBackfile
    false false false

wette1976SimplifyingComplicationAcquisition : Acquisition.SourceAcquisitionTarget
wette1976SimplifyingComplicationAcquisition =
  Acquisition.sourceAcquisitionTarget
    "Wette 1976, Journal of Symbolic Logic 41"
    "pp. 272--273; Association for Symbolic Logic meeting-report abstract"
    Acquisition.commercialBackfile
    Acquisition.publisherBackfile
    false false false

wette1974ContradictionAcquisition : Acquisition.SourceAcquisitionTarget
wette1974ContradictionAcquisition =
  Acquisition.sourceAcquisitionTarget
    "Wette 1974a, International Logic Review 9"
    "pp. 51--62"
    Acquisition.interlibraryLoan
    Acquisition.nationalCatalogue
    false false false

------------------------------------------------------------------------
-- Link acquisition targets back to the typed historical source atlas.
------------------------------------------------------------------------

canonicalSystemSource : Source.WetteSource
canonicalSystemSource = Source.wette1974CanonicalSystemAbstract

simplifyingComplicationSource : Source.WetteSource
simplifyingComplicationSource = Source.wette1976SimplifyingComplicationAbstract

contradictionPaperSource : Source.WetteSource
contradictionPaperSource = Source.wette1974Contradiction

------------------------------------------------------------------------
-- Boundary: locating the issue/backfile or an ILL route does not yet justify
-- upgrading the source-verification or historical-recovery flags.
------------------------------------------------------------------------

record WettePrimaryTextAcquisitionBoundary : Set where
  constructor wettePrimaryTextAcquisitionBoundary
  field
    jslBackfileRouteLocated : Bool
    jslBackfileRouteLocatedIsTrue : jslBackfileRouteLocated ≡ true

    internationalLogicReviewILLRouteLocated : Bool
    internationalLogicReviewILLRouteLocatedIsTrue :
      internationalLogicReviewILLRouteLocated ≡ true

    jslPrimaryTextAlreadyInspected : Bool
    jslPrimaryTextAlreadyInspectedIsFalse :
      jslPrimaryTextAlreadyInspected ≡ false

    internationalLogicReviewPrimaryTextAlreadyInspected : Bool
    internationalLogicReviewPrimaryTextAlreadyInspectedIsFalse :
      internationalLogicReviewPrimaryTextAlreadyInspected ≡ false

    acquisitionRouteAloneUpgradesHistoricalSemantics : Bool
    acquisitionRouteAloneUpgradesHistoricalSemanticsIsFalse :
      acquisitionRouteAloneUpgradesHistoricalSemantics ≡ false

canonicalWettePrimaryTextAcquisitionBoundary :
  WettePrimaryTextAcquisitionBoundary
canonicalWettePrimaryTextAcquisitionBoundary =
  wettePrimaryTextAcquisitionBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
