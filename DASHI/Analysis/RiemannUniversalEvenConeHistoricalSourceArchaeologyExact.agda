module DASHI.Analysis.RiemannUniversalEvenConeHistoricalSourceArchaeologyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannUniversalEvenConeLeanSourceCustodyExact as Custody

------------------------------------------------------------------------
-- HISTORICAL SOURCE ARCHAEOLOGY FOR THE UNIVERSAL EVEN-CONE LEAN OWNER
--
-- The Agda custody owner records two historical theorem names but no fetchable
-- Lean source.  This owner records the additional repository archaeology so we
-- do not repeatedly mistake the retained Aristotle aggregate for the missing RH
-- proof.
--
-- Checked connected dashi_lean4 branch surface (2026-09-15):
--   * main
--   * agent/monster3b-fdrep-groupalgebra-adapter
--   * agent/monster3b-phi3-power-basis
--   * agent/monster-character-determination-mathlib
--   * agent/rsa-consumer-kernel-bypass
--   * agent/toe-proof-debt-router-20260915
--   * codex/form-constants-aristotle-artifacts
--
-- The retained Aristotle branch is an ancestor of current main.  Its fetched
-- `20260604_070337_allm_20260604_070337.txt` is a selected aggregate from an
-- original Aristotle archive.  That selected aggregate contains no occurrence
-- of either cited RH theorem name and no Riemann source among its listed files.
--
-- Crucially, the aggregate DOES preserve a content-addressed acquisition lead:
-- the original archive filename plus CID/IPFS metadata.  Those archive bytes
-- have not been acquired here.  Therefore the next provenance action is archive
-- recovery, not a claim of theorem absence and not immediate reproof.
------------------------------------------------------------------------

custodyBoundary : Custody.UniversalEvenConeLeanSourceCustodyBoundary
custodyBoundary = Custody.canonicalUniversalEvenConeLeanSourceCustodyBoundary

record HistoricalAristotleArchivePointer : Set where
  constructor historical-aristotle-archive-pointer
  field
    retainedBranch : String
    retainedBranchCommit : String
    aggregatePath : String
    sourceArchiveName : String
    cid : String
    ipfs : String
    witness : String
open HistoricalAristotleArchivePointer public

currentHistoricalAristotleArchivePointer : HistoricalAristotleArchivePointer
currentHistoricalAristotleArchivePointer =
  historical-aristotle-archive-pointer
    "codex/form-constants-aristotle-artifacts"
    "72734285fd83387837e0025eb51a93b63629a0b9"
    "20260604_070337_allm_20260604_070337.txt"
    "360d39a0-6c5e-49d6-8ff0-8fefe5d8ba01-aristotle.tar.gz"
    "bafkc290d3fc4b9a3407e96b30667bdb7b33"
    "QmTYUgbQqNe9aAew9ycG1rsrx7U3rcxSYqH78oMfjjvKEz"
    "c290d3fc4b9a3407e96b30667bdb7b33ac0328210395f7f1860378e161654208"

record UniversalEvenConeHistoricalSourceArchaeologyBoundary : Set where
  constructor universal-even-cone-historical-source-archaeology-boundary
  field
    currentLeanBranchesEnumerated : Bool
    retainedAristotleBranchChecked : Bool
    retainedAristotleBranchIsAncestorOfMain : Bool
    retainedAggregateFetched : Bool

    citedEvenConeTheoremFoundInAggregate : Bool
    citedPrimeTheoremFoundInAggregate : Bool
    rHSourceFileListedInAggregate : Bool

    originalAristotleArchivePointerRecovered : Bool
    originalAristotleArchiveBytesAcquired : Bool
    originalArchiveContentsSearched : Bool

    archiveSearchMissProvesTheoremAbsent : Bool
    aggregateSourceClaimCreatesLeanCustody : Bool
    archivePointerCreatesKernelReceipt : Bool

    archiveRecoveryPrecedesMinimalReproofProbe : Bool
    minimalReproofDominatesArchiveRecovery : Bool
open UniversalEvenConeHistoricalSourceArchaeologyBoundary public

canonicalUniversalEvenConeHistoricalSourceArchaeologyBoundary :
  UniversalEvenConeHistoricalSourceArchaeologyBoundary
canonicalUniversalEvenConeHistoricalSourceArchaeologyBoundary =
  universal-even-cone-historical-source-archaeology-boundary
    true
    true
    true
    true
    false
    false
    false
    true
    false
    false
    false
    false
    false
    true
    false

data UniversalEvenConeHistoricalSourceResidual : Set where
  acquireOriginalAristotleArchiveBytes : UniversalEvenConeHistoricalSourceResidual
  verifyArchiveAgainstRecordedWitness : UniversalEvenConeHistoricalSourceResidual
  searchArchiveForCitedTheoremNames : UniversalEvenConeHistoricalSourceResidual
  recoverOwningLeanModuleAndTaperDefinition : UniversalEvenConeHistoricalSourceResidual
  obtainHistoricalKernelReceiptOrRebuildInPinnedEnvironment : UniversalEvenConeHistoricalSourceResidual
  attemptMinimalSourceBoundReproofOnlyIfArchiveRecoveryFails : UniversalEvenConeHistoricalSourceResidual

firstUniversalEvenConeHistoricalSourceResidual : UniversalEvenConeHistoricalSourceResidual
firstUniversalEvenConeHistoricalSourceResidual = acquireOriginalAristotleArchiveBytes
