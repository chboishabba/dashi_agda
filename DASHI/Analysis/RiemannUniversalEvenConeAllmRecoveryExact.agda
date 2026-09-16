module DASHI.Analysis.RiemannUniversalEvenConeAllmRecoveryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- RECOVERED ARISTOTLE ALLM EVIDENCE
--
-- The historical Aristotle intake had recorded a local path to
--   20260604_070337_allm_20260604_070337.txt
-- and a durable archive/CID/witness tuple, while the original tarball bytes
-- remained unavailable.
--
-- The dashi_lean4 repository now contains that exact allm evidence file.  Its
-- metadata reproduces the same archive name, CID, witness, selected-file list,
-- Lean v4.28.0 toolchain and mathlib v4.28.0 manifest.  Direct searches of this
-- recovered aggregate find neither historical RH theorem name nor the tokens
-- `Riemann`, `Weil`, or `taper`.
--
-- This proves only that the SELECTED ALLM AGGREGATE lacks the RH source.  It
-- does not prove that the original Aristotle tarball lacked additional files,
-- that the historical theorem never existed, or that another Aristotle run did
-- not contain it.  The tarball remains the first unpaid acquisition object.
------------------------------------------------------------------------

record RecoveredAllmEvidence : Set where
  constructor recovered-allm-evidence
  field
    repository : String
    ref : String
    path : String
    gitBlob : String
    archiveName : String
    cidLabel : String
    witnessSHA256 : String
    ipfsCIDv0 : String
    leanToolchain : String
    mathlibInputRev : String
open RecoveredAllmEvidence public

currentRecoveredAllmEvidence : RecoveredAllmEvidence
currentRecoveredAllmEvidence =
  recovered-allm-evidence
    "chboishabba/dashi_lean4"
    "4413cb455d5264db64cabe0356f74dd3d0112a4c"
    "20260604_070337_allm_20260604_070337.txt"
    "b0c0dc1135faa3520d0086f89a8a78807d6d38e0"
    "360d39a0-6c5e-49d6-8ff0-8fefe5d8ba01-aristotle.tar.gz"
    "bafkc290d3fc4b9a3407e96b30667bdb7b33"
    "c290d3fc4b9a3407e96b30667bdb7b33ac0328210395f7f1860378e161654208"
    "QmTYUgbQqNe9aAew9ycG1rsrx7U3rcxSYqH78oMfjjvKEz"
    "leanprover/lean4:v4.28.0"
    "v4.28.0"

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SelectedAggregateAbsenceMeansArchiveAbsence : Set where
data SearchMissMeansTheoremNeverExisted : Set where
data RecoveredMetadataCreatesTaperProof : Set where

selectedAggregateAbsenceDoesNotMeanArchiveAbsence :
  SelectedAggregateAbsenceMeansArchiveAbsence -> ⊥
selectedAggregateAbsenceDoesNotMeanArchiveAbsence ()

searchMissDoesNotMeanTheoremNeverExisted :
  SearchMissMeansTheoremNeverExisted -> ⊥
searchMissDoesNotMeanTheoremNeverExisted ()

recoveredMetadataDoesNotCreateTaperProof :
  RecoveredMetadataCreatesTaperProof -> ⊥
recoveredMetadataDoesNotCreateTaperProof ()

record AllmRecoveryBoundary : Set where
  constructor allm-recovery-boundary
  field
    allmPathPreviouslyRecorded : Bool
    allmBytesNowRecoveredInRepository : Bool
    archiveIdentityTupleMatchesPriorReceipt : Bool
    selectedFileListRecovered : Bool
    pinnedLeanToolchainRecovered : Bool
    pinnedMathlibRevisionRecovered : Bool

    literalWeilSameOrdinateEvenConeFoundInAllm : Bool
    primeEvenConeUnreachableFoundInAllm : Bool
    riemannTokenFoundInAllm : Bool
    weilTokenFoundInAllm : Bool
    taperTokenFoundInAllm : Bool

    originalAristotleTarballBytesAcquired : Bool
    originalTarballContentsSearched : Bool
    historicalUniversalTaperSourceRecovered : Bool
    sameObjectPoleQuotientTransportPaid : Bool
    nextResidual : String
open AllmRecoveryBoundary public

canonicalAllmRecoveryBoundary : AllmRecoveryBoundary
canonicalAllmRecoveryBoundary =
  allm-recovery-boundary
    true true true true true true
    false false false false false
    false false false false
    "recover the original Aristotle tarball bytes identified by the archive/CID/witness tuple, verify the recovered bytes against preserved integrity metadata, and search the complete archive for the historical universal-even-cone theorem/taper owner. Absence from this selected allm aggregate is not archive-level absence."
