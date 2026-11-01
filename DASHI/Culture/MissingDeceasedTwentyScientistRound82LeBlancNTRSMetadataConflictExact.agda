module DASHI.Culture.MissingDeceasedTwentyScientistRound82LeBlancNTRSMetadataConflictExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ROUND 82 / NTRS CATALOG-vs-ATTACHMENT METADATA CONFLICT
--
-- NTRS record 20240010391 currently exposes catalog meeting metadata for a
-- NASA Glenn inquiry on Sandia radiation-testing capabilities (2026-05-27),
-- while the attached presentation itself identifies the 2024 NASA Fission
-- Instrumentation and Controls Workshop, Cleveland, 2024-08-20..22.
--
-- Preserve both source-bound coordinates.  Do not silently overwrite one with
-- the other without a provenance/revision receipt.
------------------------------------------------------------------------

record MetadataCoordinate : Set where
  constructor metadataCoordinate
  field
    carrier : String
    fieldName : String
    fieldValue : String

open MetadataCoordinate public

catalogMeeting : MetadataCoordinate
catalogMeeting = metadataCoordinate
  "NASA NTRS record 20240010391"
  "meeting"
  "NASA Glenn Inquiry on Sandia Radiation Testing Capabilities; start date 2026-05-27"

attachmentMeeting : MetadataCoordinate
attachmentMeeting = metadataCoordinate
  "FSPWorkshop_GRCThinFilmsJWrbanek.pdf attached to NTRS 20240010391"
  "title-slide meeting"
  "2024 NASA Fission Instrumentation and Controls Workshop; Cleveland; 2024-08-20..22"

catalogMeetingMetadataPaid : Bool
catalogMeetingMetadataPaid = true

attachmentWorkshopMetadataPaid : Bool
attachmentWorkshopMetadataPaid = true

metadataConflictVisible : Bool
metadataConflictVisible = true

catalogDoesNotOverwriteAttachment : Bool
catalogDoesNotOverwriteAttachment = true

attachmentDoesNotOverwriteCatalog : Bool
attachmentDoesNotOverwriteCatalog = true

conflictDoesNotImplyFabrication : Bool
conflictDoesNotImplyFabrication = true

conflictDoesNotPayRevisionHistory : Bool
conflictDoesNotPayRevisionHistory = true

secondRetainedScientistPaid : Bool
secondRetainedScientistPaid = false

h2Paid : Bool
h2Paid = false

h3Paid : Bool
h3Paid = false

record Round82Boundary : Set where
  constructor round82Boundary
  field
    catalogCoordinatePaid : Bool
    attachmentCoordinatePaid : Bool
    conflictRetained : Bool
    provenanceNeededForReconciliation : Bool
    h2PromotionPaid : Bool
    h3PromotionPaid : Bool

canonicalRound82Boundary : Round82Boundary
canonicalRound82Boundary = round82Boundary
  true true true true false false
