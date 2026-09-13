module DASHI.Wikimedia.IbrahimFirstLinkHistoricalChunkLineageDeltaExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.IbrahimFirstLinkHistoricalSnapshotProvenanceResidualExact as Historical
import DASHI.Wikimedia.IbrahimFirstLinkHistoricalDumpCandidateStrengtheningExact as Candidate

------------------------------------------------------------------------
-- THIN DELTA: RAW-CHUNK -> PAGE-ALIGNED XML LINEAGE
--
-- The public old-code tree contains the missing repair program.  It enumerates
-- smallaa..smalleh, reads the start of each next raw chunk through its first
-- </page>, appends that suffix to the current chunk, then renames the current
-- chunk to .xml.  This pays the repair transform, but NOT the upstream raw split
-- command, byte/line size, exact source dump hash, chunk hashes, or execution.
------------------------------------------------------------------------

historicalBoundary : Historical.HistoricalSnapshotProvenanceBoundary
historicalBoundary = Historical.canonicalHistoricalSnapshotProvenanceBoundary

candidateBoundary : Candidate.CandidateStrengtheningBoundary
candidateBoundary = Candidate.canonicalCandidateStrengtheningBoundary

chopWikiSource : Attribution.AttributedSource
chopWikiSource = Attribution.mkNoDOISource
  "Mark Ibrahim"
  "code/old_code/process/chop_wiki.py"
  "marksibrahim/wikipedia_network; blob bbbf7667e430e7d520535ae2c88f528960884aaa"
  "2015"
  "https://github.com/marksibrahim/wikipedia_network/blob/master/code/old_code/process/chop_wiki.py"
  (Attribution.namedSourceKind "research preprocessing source code")
  "primary preprocessing code paying the raw smallxx chunk to page-aligned .xml repair algorithm; does not identify the upstream split command or prove execution on the published FLN input"
  Attribution.publicAttribution

record ChunkRepairReceipt : Set where
  constructor chunk-repair-receipt
  field
    rawChunkPrefix : String
    firstRawChunk : String
    lastRawChunk : String
    enumeratedChunkCount : Nat
    repairRule : String
    repairedSuffix : String
    localDataPath : String
    repairBlobSha : String
    rawSplitCommandRecovered : Bool
    rawSplitUnitRecovered : Bool
    rawSplitSizeRecovered : Bool
    rawChunkHashesRecovered : Bool
    repairExecutionReceiptRecovered : Bool
    repairedChunksSameObjectWithConstructorInputsPaid : Bool
open ChunkRepairReceipt public

canonicalChunkRepairReceipt : ChunkRepairReceipt
canonicalChunkRepairReceipt = chunk-repair-receipt
  "small"
  "smallaa"
  "smalleh"
  112
  "for each current raw chunk, append from the next raw chunk through its first </page>, then rename current file with .xml suffix"
  ".xml"
  "/users/m/s/msibrahi/full_wiki_data/"
  "bbbf7667e430e7d520535ae2c88f528960884aaa"
  false false false false false false

------------------------------------------------------------------------
-- This narrows the remaining same-object path.
------------------------------------------------------------------------

data HistoricalChunkPaymentStage : Set where
  dumpCandidateIdentified : HistoricalChunkPaymentStage
  rawSplitAlgorithmUnpaid : HistoricalChunkPaymentStage
  pageBoundaryRepairAlgorithmPaid : HistoricalChunkPaymentStage
  repairExecutionUnpaid : HistoricalChunkPaymentStage
  constructorConsumptionCodePaid : HistoricalChunkPaymentStage
  publishedGraphSameObjectUnpaid : HistoricalChunkPaymentStage

record ChunkLineageDeltaBoundary : Set where
  constructor chunk-lineage-delta-boundary
  field
    exactRepairSourcePinned : Bool
    rawChunkNameRangePaid : Bool
    repairedChunkCountPaid : Bool
    pageBoundaryRepairSemanticsPaid : Bool
    rawSplitCommandStillUnresolved : Bool
    rawSplitParametersStillUnresolved : Bool
    executionStillUnresolved : Bool
    exactChunkHashesStillUnresolved : Bool
    publishedInputIdentityStillUnresolved : Bool
    suffixPatternPromotedToGNUCommand : Bool
open ChunkLineageDeltaBoundary public

canonicalChunkLineageDeltaBoundary : ChunkLineageDeltaBoundary
canonicalChunkLineageDeltaBoundary = chunk-lineage-delta-boundary
  true true true true true true true true true false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data FilenamePatternMeansGNUDefaultSplit : Set where
data RepairCodeMeansRepairWasExecuted : Set where
data RepairPathMeansExactInputDump : Set where
data RepairedChunkCountMeansChunkHashesKnown : Set where

gnuStyleSuffixPatternDoesNotProveSplitCommand : FilenamePatternMeansGNUDefaultSplit → ⊥
gnuStyleSuffixPatternDoesNotProveSplitCommand ()

repairCodeDoesNotProveExecution : RepairCodeMeansRepairWasExecuted → ⊥
repairCodeDoesNotProveExecution ()

localPathDoesNotIdentifyUpstreamDump : RepairPathMeansExactInputDump → ⊥
localPathDoesNotIdentifyUpstreamDump ()

chunkCountDoesNotCreateHashes : RepairedChunkCountMeansChunkHashesKnown → ⊥
chunkCountDoesNotCreateHashes ()

remainingChunkLineagePayment : String
remainingChunkLineagePayment =
  "recover the command/process that produced raw smallaa..smalleh from the whole dump (including unit/size/order), or independently reconstruct a byte/page-identical raw-chunk sequence; recover hashes or another same-object receipt for raw/repaired chunks; then execute the pinned repair + parser + constructor and compare against the public FLN artifact."
