module DASHI.Physics.Optics.BerkeleyPLDArchiveRunMetadataBoundaryExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Optics.BerkeleyPLD100kReleaseProvenanceExact as Release

------------------------------------------------------------------------
-- RELEASED-ARCHIVE RUN-METADATA BOUNDARY
--
-- The released capture program constructs metadata from DATETIME, source,
-- number/start index, RGB format and exposure_times, then writes metadata.json
-- into the capture destination.  Therefore a same-run metadata.json from the
-- released archive is exactly the right object to weld exposure configuration
-- to archive bytes.
--
-- The public Drive RML/Diffuser folders expose only four very large 25k ZIP
-- chunks per system at folder level; no sidecar metadata.json is exposed there.
-- The current connector cannot inspect 60--70 GB ZIP internals.  Drive modified
-- times are also not a valid substitute: RML chunks and diffuser chunks have
-- materially different packaging/upload dates despite belonging to the same
-- published parallel dataset.
--
-- Consequently publication-level 100k acquisition provenance remains paid, but
-- exact byte-archive same-run exposure identity remains fail-closed until a run
-- manifest is recovered from inside an archive or separately published.
------------------------------------------------------------------------

captureMetadataFileName : String
captureMetadataFileName = "metadata.json"

captureMetadataIncludesExposureTimes : Bool
captureMetadataIncludesExposureTimes = true

rmlChunkCount : Nat
rmlChunkCount = 4

diffuserChunkCount : Nat
diffuserChunkCount = 4

rml0k25kBytes : String
rml0k25kBytes = "60039881492"
rml0k25kDriveModified : String
rml0k25kDriveModified = "2026-05-03T18:13:08.510Z"

diffuser0k25kBytes : String
diffuser0k25kBytes = "69546860375"
diffuser0k25kDriveModified : String
diffuser0k25kDriveModified = "2026-08-01T03:41:28.357Z"

folderLevelSidecarMetadataExposed : Bool
folderLevelSidecarMetadataExposed = false

archiveInternalRunMetadataInspected : Bool
archiveInternalRunMetadataInspected = false

driveModifiedTimeIdentifiesCaptureConfiguration : Bool
driveModifiedTimeIdentifiesCaptureConfiguration = false

exactArchiveRunLogRecovered : Bool
exactArchiveRunLogRecovered = false

exactArchiveExposureSameRunPaid : Bool
exactArchiveExposureSameRunPaid = false

record BerkeleyPLDArchiveRunMetadataBoundary : Set where
  field
    metadataName : String
    metadataCarriesExposureTimes : Bool
    rmlChunks : Nat
    diffuserChunks : Nat
    folderSidecar : Bool
    archiveInternalsInspected : Bool
    driveTimestampIdentifiesCapture : Bool
    runLogRecovered : Bool
    sameRunExposurePaid : Bool

open BerkeleyPLDArchiveRunMetadataBoundary public

currentBerkeleyPLDArchiveRunMetadataBoundary : BerkeleyPLDArchiveRunMetadataBoundary
currentBerkeleyPLDArchiveRunMetadataBoundary = record
  { metadataName = captureMetadataFileName
  ; metadataCarriesExposureTimes = captureMetadataIncludesExposureTimes
  ; rmlChunks = rmlChunkCount
  ; diffuserChunks = diffuserChunkCount
  ; folderSidecar = folderLevelSidecarMetadataExposed
  ; archiveInternalsInspected = archiveInternalRunMetadataInspected
  ; driveTimestampIdentifiesCapture = driveModifiedTimeIdentifiesCaptureConfiguration
  ; runLogRecovered = exactArchiveRunLogRecovered
  ; sameRunExposurePaid = exactArchiveExposureSameRunPaid
  }

-- Release remains authoritative for the published 100k acquisition identity.
-- This module narrows the stronger byte-level obligation; it does not override
-- or weaken that paid publication-level provenance.
