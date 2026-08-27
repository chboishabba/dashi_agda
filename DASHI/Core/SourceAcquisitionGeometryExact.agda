module DASHI.Core.SourceAcquisitionGeometryExact where

------------------------------------------------------------------------
-- SOURCE ACQUISITION GEOMETRY
--
-- Generic owner for provenance-aware historical / archival recovery.
-- Locating a bibliographic record, identifying an access route, acquiring the
-- primary text, inspecting it, and extracting a transcription are distinct
-- stages.  This module deliberately does not collapse them.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Access routes are labels for how a primary text can be obtained.
------------------------------------------------------------------------

data AccessRoute : Set where
  directDigitalArchive : AccessRoute
  publisherBackfile : AccessRoute
  commercialBackfile : AccessRoute
  interlibraryLoan : AccessRoute
  nationalCatalogue : AccessRoute
  physicalHolding : AccessRoute

record SourceAcquisitionTarget : Set where
  constructor sourceAcquisitionTarget
  field
    citationLabel : String
    pageLocator : String
    primaryRoute : AccessRoute
    alternateRoute : AccessRoute
    fullTextAcquired : Bool
    primaryTextInspected : Bool
    transcriptionExtracted : Bool

open SourceAcquisitionTarget public

------------------------------------------------------------------------
-- Acquisition states are intentionally monotone only when evidence is supplied.
-- Merely knowing a route does not manufacture the text or an inspection receipt.
------------------------------------------------------------------------

record SourceAcquisitionBoundary : Set where
  constructor sourceAcquisitionBoundary
  field
    bibliographicMetadataEqualsFullTextAccess : Bool
    bibliographicMetadataEqualsFullTextAccessIsFalse :
      bibliographicMetadataEqualsFullTextAccess ≡ false

    accessRouteEqualsPrimaryTextInspection : Bool
    accessRouteEqualsPrimaryTextInspectionIsFalse :
      accessRouteEqualsPrimaryTextInspection ≡ false

    primaryTextInspectionEqualsTranscription : Bool
    primaryTextInspectionEqualsTranscriptionIsFalse :
      primaryTextInspectionEqualsTranscription ≡ false

    interlibraryLoanIsLegitimatePrimaryAcquisitionRoute : Bool
    interlibraryLoanIsLegitimatePrimaryAcquisitionRouteIsTrue :
      interlibraryLoanIsLegitimatePrimaryAcquisitionRoute ≡ true

canonicalSourceAcquisitionBoundary : SourceAcquisitionBoundary
canonicalSourceAcquisitionBoundary =
  sourceAcquisitionBoundary
    false refl
    false refl
    false refl
    true refl
