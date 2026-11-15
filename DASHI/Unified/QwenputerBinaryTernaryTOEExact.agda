module DASHI.Unified.QwenputerBinaryTernaryTOEExact where

-- Re-export ONLY actual finite DASHI witnesses to the TOE import graph.
-- External architecture: Divyansh Agrawal, Qwenputer (2026),
-- https://github.com/divagr18/qwenputer
-- The Agda results below are repo-native abstractions, not source binaries.
-- Existing binary/ternary owner is reused rather than replaced.

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Maybe using (just)

import DASHI.ComputerScience.QwenputerGatedDeltaArchitectureExact as GDN
import DASHI.ComputerScience.QwenputerRv32LayerScheduleSourceExact as Layers
import DASHI.ComputerScience.QwenputerOneHotDeltaMatrixRefinementExact as Matrix
import DASHI.ComputerScience.QwenputerRv32RecordCommitExact as Records
import DASHI.ComputerScience.QwenputerBinaryTernaryRamTraceSimulationExact as Trace
import DASHI.ComputerScience.QwenputerBinary32Framed27CodecExact as Word32
import DASHI.ComputerScience.QwenputerHybridStateAndFileStoreExact as Store
import DASHI.ComputerScience.BinaryBalancedTernarySubcarrierExact as Binary
import DASHI.ComputerScience.ShorStandardBinaryTernaryStoredProgramComputerExact as BinaryTernary

toeQwenputerSourceIdentity : GDN.SourceIdentity
toeQwenputerSourceIdentity = GDN.qwenputerSource

toeQwenputerSourceArchitecture : GDN.Rv32SourceParameters
toeQwenputerSourceArchitecture = GDN.rv32ReportedParameters

toeQwenputerProofBoundary : GDN.ArchitectureBoundary
toeQwenputerProofBoundary = GDN.canonicalArchitectureBoundary

toeQwenputerReadAfterWrite :
  (store : GDN.Ram Bool) (location : GDN.Location) (bit : Bool) →
  GDN.readRam (GDN.writeRam store location bit) location ≡ bit
toeQwenputerReadAfterWrite = GDN.readWriteSame

toeQwenputerDecodedTernaryWrite :
  (store : GDN.Ram Bool) (location : GDN.Location) (bit : Bool) →
  Binary.decodeEmbeddedBit
    (GDN.readRam
      (GDN.writeRam (GDN.embedBinaryRam store) location
        (Binary.embedBit bit))
      location)
  ≡ bit
toeQwenputerDecodedTernaryWrite = GDN.decodedEmbeddedWrite

toeQwenputerFiniteFileGetAfterPut :
  (store : Store.FileStore) (name : Store.FileName)
  (value : Store.FileContents) →
  Store.get (Store.put store name value) name ≡
    just value
toeQwenputerFiniteFileGetAfterPut = Store.getAfterPut

-- Refer to the real binary/ternary stored-program theorem owner.
toePriorBinaryTernaryOrder15Equal :
  BinaryTernary.order15BinaryFinal ≡ BinaryTernary.order15TernaryFinal
toePriorBinaryTernaryOrder15Equal =
  BinaryTernary.order15BinaryAndTernaryExecutionEqual

toeQwenputerSourceHeadSum : Layers.reportedKeyHeadTotal ≡ 99
toeQwenputerSourceHeadSum = Layers.keyHeadSumMatchesAuthor


------------------------------------------------------------------------
-- New source-accurate and codec theorem consumers. All source-written:
-- use the pinned toolchain before claiming kernel-verified results.
------------------------------------------------------------------------

toeOneHotDeltaRefinesRAM :
  (D : Matrix.DeltaScalar) {Column : Set}
  (matrix : Matrix.Matrix D Column) (selected : GDN.Location)
  (value : Matrix.Vector D Column)
  (queried : GDN.Location) (col : Column) →
  Matrix.oneHotMatrixUpdate D matrix selected value queried col
  ≡ GDN.writeRam (λ a → matrix a col) selected (value col) queried
toeOneHotDeltaRefinesRAM = Matrix.refineMatrixWrite

toeRv32RecordCommitsAtLastToken :
  {State : Set} (execute : State → State)
  (rec : Records.SourceRecord) (s : State) →
  Records.runTokens execute (Records.emitSourceRecord rec) s ≡ execute s
toeRv32RecordCommitsAtLastToken = Records.eachSourceRecordCommitsOnce

toeAllBinaryTernaryWriteTraces :
  (commands : Trace.Writes) (store : GDN.Ram Bool)
  (queried : GDN.Location) →
  Binary.decodeEmbeddedBit
    (Trace.runTernary commands (GDN.embedBinaryRam store) queried)
    ≡ Trace.runBinary commands store queried
toeAllBinaryTernaryWriteTraces =
  Trace.binaryTernaryCompleteWriteTrace

toeBinary32Ternary27RoundTrip :
  (word : Word32.BinaryWord32) →
  Word32.decode32 (Word32.encode32 word) ≡ word
toeBinary32Ternary27RoundTrip = Word32.word32RoundTrip


toeAllAbstractDeltaMatrixWritesCommute :
  (D : Matrix.DeltaScalar) {Column : Set}
  (writes : Matrix.MatrixWrite D Column)
  (matrix : Matrix.Matrix D Column)
  (queried : GDN.Location) (col : Column) →
  Matrix.runMatrix D writes matrix queried col ≡
    Matrix.runVectorRAM D writes (Matrix.matrixAsRam D matrix)
      queried col
toeAllAbstractDeltaMatrixWritesCommute =
  Matrix.matrixAndRamSameAfterEveryWrite


toeArbitraryChipBurstMutesLanguage :
  {L C : Set} (fuel : Nat) (f : C → C)
  (state : Store.HybridState L C) →
  Store.language (Store.repeatCircuit fuel f state)
    ≡ Store.language state
toeArbitraryChipBurstMutesLanguage =
  Store.allCircuitStepsMuteLanguage

toeP3SourceCaptureBudget :
  Layers.bytesPerToken Layers.p3ReportedTextBridge
    * Layers.maxCapturedTokens Layers.p3ReportedTextBridge
    ≡ 1280
toeP3SourceCaptureBudget = Layers.p3CaptureMaximumBytes
