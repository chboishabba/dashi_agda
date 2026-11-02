module DASHI.ComputerScience.QwenputerGatedDeltaArchitectureExact where

-- SOURCE / OWNERSHIP
-- Divyansh Agrawal, "Qwenputer: a computer compiled into the weights of a
-- pretrained language model" (2026), v0.1.0, MIT.
-- https://github.com/divagr18/qwenputer
-- https://divagr.com/blog/qwenputer (22 October 2026)
-- https://github.com/divagr18/qwenputer/blob/main/experimental/riscv/docs/rv32.md
-- https://github.com/divagr18/qwenputer/blob/main/docs/q35.md
-- Delta-rule associative-memory ancestry: Imanol Schlag, Kazuki Irie and
-- Jürgen Schmidhuber, "Linear Transformers Are Secretly Fast Weight
-- Programmers", ICML 2021.
--
-- The executable finite RAM, trace, and binary/ternary lemmas below are
-- DASHI reconstructions and extensions, NOT imported Agrawal proof terms.
-- They do NOT prove equivalence to the released Qwenputer bf16 checkpoint,
-- RISC-V ISA, Triton executor, reference bridge, or empirical benchmarks.
-- Existing DASHI ownership: TemporalStorageFibreExact,
-- BinaryBalancedTernarySubcarrierExact, TinyRadixNeutralRegisterMachineExact,
-- ShorStandardBinaryTernaryStoredProgramComputerExact and Tekum.
-- No claim that ternary is Qwenputer's native numerical implementation.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.String using (String)

import DASHI.ComputerScience.BinaryBalancedTernarySubcarrierExact as Binary
import DASHI.ComputerScience.TemporalStorageFibreExact as Storage
import DASHI.ComputerScience.TinyRadixNeutralRegisterMachineExact as Machine
import DASHI.Foundations.SSPTritCarrier as Trit

------------------------------------------------------------------------
-- A small FINITE address geometry: two head classes, three rows per head.
-- Qwenputer uses many more heads and rows; these constructors test the
-- actual one-hot selection law, not the published memory capacity.
------------------------------------------------------------------------

data Head : Set where
  dataHead : Head
  registerHead : Head

data Row : Set where
  row0 row1 row2 : Row

record Location : Set where
  constructor location
  field
    head : Head
    row : Row
open Location public

headEqual : Head → Head → Bool
headEqual dataHead dataHead = true
headEqual dataHead registerHead = false
headEqual registerHead dataHead = false
headEqual registerHead registerHead = true

rowEqual : Row → Row → Bool
rowEqual row0 row0 = true
rowEqual row0 row1 = false
rowEqual row0 row2 = false
rowEqual row1 row0 = false
rowEqual row1 row1 = true
rowEqual row1 row2 = false
rowEqual row2 row0 = false
rowEqual row2 row1 = false
rowEqual row2 row2 = true

sameLocation : Location → Location → Bool
sameLocation (location h r) (location k s) with headEqual h k | rowEqual r s
... | true | true = true
... | _ | _ = false

sameLocationRefl : (a : Location) → sameLocation a a ≡ true
sameLocationRefl (location dataHead row0) = refl
sameLocationRefl (location dataHead row1) = refl
sameLocationRefl (location dataHead row2) = refl
sameLocationRefl (location registerHead row0) = refl
sameLocationRefl (location registerHead row1) = refl
sameLocationRefl (location registerHead row2) = refl

Ram : Set → Set
Ram V = Location → V

readRam : {V : Set} → Ram V → Location → V
readRam store address = store address

-- This is the EXACT discrete one-hot overwrite semantics of a delta-rule
-- head with alpha=beta=1, a one-hot key/query, and exact scalar arithmetic.
-- Matrix arithmetic/normalisation/rounding require further compiler lemmas.
writeRam : {V : Set} → Ram V → Location → V → Ram V
writeRam store selected value queried with sameLocation selected queried
... | true = value
... | false = store queried

readWriteSame :
  {V : Set} (store : Ram V) (address : Location) (value : V) →
  readRam (writeRam store address value) address ≡ value
readWriteSame store address value
  rewrite sameLocationRefl address = refl

readWriteOther :
  {V : Set} (store : Ram V) (selected queried : Location) (value : V) →
  sameLocation selected queried ≡ false →
  readRam (writeRam store selected value) queried ≡ readRam store queried
readWriteOther store selected queried value different
  rewrite different = refl

-- Explicit disjoint-head witnesses, including one-hot noninterference.
dataAndRegisterAreDifferent :
  (r s : Row) →
  sameLocation (location dataHead r) (location registerHead s) ≡ false
dataAndRegisterAreDifferent row0 row0 = refl
dataAndRegisterAreDifferent row0 row1 = refl
dataAndRegisterAreDifferent row0 row2 = refl
dataAndRegisterAreDifferent row1 row0 = refl
dataAndRegisterAreDifferent row1 row1 = refl
dataAndRegisterAreDifferent row1 row2 = refl
dataAndRegisterAreDifferent row2 row0 = refl
dataAndRegisterAreDifferent row2 row1 = refl
dataAndRegisterAreDifferent row2 row2 = refl

registerHeadUnchangedAfterDataWrite :
  {V : Set} (store : Ram V) (r s : Row) (value : V) →
  readRam (writeRam store (location dataHead r) value)
    (location registerHead s)
  ≡ readRam store (location registerHead s)
registerHeadUnchangedAfterDataWrite store r s value =
  readWriteOther store (location dataHead r) (location registerHead s)
    value (dataAndRegisterAreDifferent r s)

------------------------------------------------------------------------
-- Token-fed RAM semantics. ADDR picks a key, VAL writes the value, STEP
-- terminates the instruction. This is a bounded abstract trace protocol.
-- It is not a byte-for-byte decoding of Qwenputer's real tokenizer/firmware.
------------------------------------------------------------------------

data TraceToken : Set where
  ADDR : Location → TraceToken
  VAL : Bool → TraceToken
  STEP BOOT HALT : TraceToken

record TraceState : Set where
  constructor traceState
  field
    ram : Ram Bool
    pendingAddress : Maybe Location
    programCounter : Nat
    instructionsEnded : Nat
    stopped : Bool
open TraceState public

advance : TraceState → TraceToken → TraceState
advance s (ADDR a) =
  traceState (ram s) (just a) (programCounter s)
    (instructionsEnded s) (stopped s)
advance s (VAL bit) with pendingAddress s
... | nothing = s
... | just a =
  traceState (writeRam (ram s) a bit) (just a) (programCounter s)
    (instructionsEnded s) (stopped s)
advance s STEP =
  traceState (ram s) nothing (suc (programCounter s))
    (suc (instructionsEnded s)) (stopped s)
advance s BOOT =
  traceState (ram s) nothing 0 0 false
advance s HALT =
  traceState (ram s) nothing (programCounter s)
    (instructionsEnded s) true

runTrace : List TraceToken → TraceState → TraceState
runTrace [] s = s
runTrace (token ∷ tokens) s = runTrace tokens (advance s token)

singleWrite : TraceState → Location → Bool → TraceState
singleWrite s a bit =
  advance (advance (advance s (ADDR a)) (VAL bit)) STEP

singleWriteReadsBack :
  (s : TraceState) (a : Location) (bit : Bool) →
  readRam (ram (singleWrite s a bit)) a ≡ bit
singleWriteReadsBack s a bit =
  readWriteSame (ram s) a bit

singleWritePreservesOther :
  (s : TraceState) (a b : Location) (bit : Bool) →
  sameLocation a b ≡ false →
  readRam (ram (singleWrite s a bit)) b ≡ readRam (ram s) b
singleWritePreservesOther s a b bit neq =
  readWriteOther (ram s) a b bit neq

singleWriteAdvancesPC :
  (s : TraceState) (a : Location) (bit : Bool) →
  programCounter (singleWrite s a bit) ≡ suc (programCounter s)
singleWriteAdvancesPC s a bit = refl

singleWriteClosesPendingAddress :
  (s : TraceState) (a : Location) (bit : Bool) →
  pendingAddress (singleWrite s a bit) ≡ nothing
singleWriteClosesPendingAddress s a bit = refl

singleWriteCountsInstruction :
  (s : TraceState) (a : Location) (bit : Bool) →
  instructionsEnded (singleWrite s a bit) ≡ suc (instructionsEnded s)
singleWriteCountsInstruction s a bit = refl

------------------------------------------------------------------------
-- Reuse native binary/balanced-ternary representation ownership.
-- The zero trit stays outside the binary subcarrier; it is not ignored.
------------------------------------------------------------------------

embedBinaryRam : Ram Bool → Ram Trit.SSPTrit
embedBinaryRam store a = Binary.embedBit (store a)

decodedEmbeddedWrite :
  (store : Ram Bool) (a : Location) (bit : Bool) →
  Binary.decodeEmbeddedBit
    (readRam (writeRam (embedBinaryRam store) a (Binary.embedBit bit)) a)
  ≡ bit
decodedEmbeddedWrite store a bit
  rewrite readWriteSame (embedBinaryRam store) a (Binary.embedBit bit)
        | Binary.binaryTernaryRoundTrip bit = refl

embeddedOtherPreserved :
  (store : Ram Bool) (selected queried : Location) (bit : Bool) →
  sameLocation selected queried ≡ false →
  readRam
    (writeRam (embedBinaryRam store) selected (Binary.embedBit bit))
    queried
  ≡ Binary.embedBit (store queried)
embeddedOtherPreserved store selected queried bit neq =
  readWriteOther (embedBinaryRam store) selected queried
    (Binary.embedBit bit) neq

-- An actual reused type-level representation certificate, not just a
-- textual similarity between two encodings.
binaryTernaryCellFibre : Storage.CellRepresentationFibre Bool
binaryTernaryCellFibre = Binary.binaryInBalancedTernaryRepresentation

------------------------------------------------------------------------
-- Machine and compiler commuting-square OBLIGATION, deliberately not filled
-- for the published RISC-V core. A proof for the tiny DASHI machine would
-- not establish the RV32IM+Zba+bignum instruction semantics.
------------------------------------------------------------------------

record InstructionSimulation
  (ReferenceState CompiledState : Set) : Set where
  constructor instructionSimulation
  field
    decode : CompiledState → ReferenceState
    referenceStep : ReferenceState → ReferenceState
    compiledStep : CompiledState → CompiledState
    stepCommutes :
      (c : CompiledState) →
      decode (compiledStep c) ≡ referenceStep (decode c)
open InstructionSimulation public

-- The generic theorem consumes a *supplied* exact one-step certificate.
-- The real compiler certificate remains an explicit missing argument.
simulationTwoSteps :
  {R C : Set} (sim : InstructionSimulation R C) (c : C) →
  decode sim (compiledStep sim (compiledStep sim c))
  ≡ referenceStep sim (referenceStep sim (decode sim c))
simulationTwoSteps sim c
  rewrite stepCommutes sim (compiledStep sim c)
        | stepCommutes sim c = refl

-- Existing executable radix-neutral machine and its real run semantics
-- remain the source owner for concrete local register-machine behaviour.
tinyReferenceTwoStep :
  (s : Machine.MachineState) →
  Machine.runFuel 2 s ≡ Machine.step (Machine.step s)
tinyReferenceTwoStep s = refl

------------------------------------------------------------------------
-- SOURCE ARCHITECTURE: metadata is a recovered specification, not a proof
-- that the published circuit implements it.
------------------------------------------------------------------------

record SourceIdentity : Set where
  constructor sourceIdentity
  field
    author : String
    work : String
    edition : String
    sourceURI : String
open SourceIdentity public

qwenputerSource : SourceIdentity
qwenputerSource =
  sourceIdentity
    "Divyansh Agrawal"
    "Qwenputer: a computer compiled into the weights of a pretrained language model"
    "2026-10-22, software v0.1.0"
    "https://github.com/divagr18/qwenputer"

data Component : Set where
  baseQwen35 chip8Core rv32imCore zbaExtension bignumUnit : Component
  compiledSwiGLU compiledGatedDeltaNet oneHotRAM : Component
  ramAddressLayout registersAndPC firmwareBoot : Component
  addressValueStepProtocol textBridge tokenOwnership : Component
  qwenStateMute rmsNormBallast bf16Exactness : Component
  referenceMachine tritonExecutor snapshotAndRestore : Component
  filesystemDirectory filesystemContentHeads : Component
  filesystemAPIs oversightMonitor opaqueReasoningStudy : Component

sourceArchitectureCoverage : List Component
sourceArchitectureCoverage =
  baseQwen35 ∷ chip8Core ∷ rv32imCore ∷ zbaExtension ∷ bignumUnit
  ∷ compiledSwiGLU ∷ compiledGatedDeltaNet ∷ oneHotRAM
  ∷ ramAddressLayout ∷ registersAndPC ∷ firmwareBoot
  ∷ addressValueStepProtocol ∷ textBridge ∷ tokenOwnership
  ∷ qwenStateMute ∷ rmsNormBallast ∷ bf16Exactness
  ∷ referenceMachine ∷ tritonExecutor ∷ snapshotAndRestore
  ∷ filesystemDirectory ∷ filesystemContentHeads
  ∷ filesystemAPIs ∷ oversightMonitor ∷ opaqueReasoningStudy ∷ []

record Rv32SourceParameters : Set where
  constructor rv32SourceParameters
  field
    compiledPrelayers : Nat
    originalQwenLayers : Nat
    hiddenWidth : Nat
    vocabularyRows : Nat
    appendedSpecialRows : Nat
    maxCapturedCallTokens : Nat
    maxDecimalDigits : Nat
open Rv32SourceParameters public

rv32ReportedParameters : Rv32SourceParameters
rv32ReportedParameters =
  rv32SourceParameters 11 32 3968 478656 230324 80 62

data VerificationLevel : Set where
  provedFiniteAbstraction : VerificationLevel
  reusedInRepo : VerificationLevel
  externalAuthorReport : VerificationLevel
  openSameObjectBridge : VerificationLevel

record ArchitectureBoundary : Set where
  constructor architectureBoundary
  field
    finiteRowReadWriteLevel : VerificationLevel
    binaryTernaryRepresentationLevel : VerificationLevel
    radixNeutralMachineLevel : VerificationLevel
    siliconFreeRv32ImplementationLevel : VerificationLevel
    actualCheckpointSameObjectLevel : VerificationLevel
    floatingPointExactnessLevel : VerificationLevel
    realTokenizerProtocolLevel : VerificationLevel
    realRV32InstructionSimulationLevel : VerificationLevel
    filesystemPersistenceLevel : VerificationLevel
    monitoringClaimsLevel : VerificationLevel
open ArchitectureBoundary public

canonicalArchitectureBoundary : ArchitectureBoundary
canonicalArchitectureBoundary =
  architectureBoundary
    provedFiniteAbstraction reusedInRepo reusedInRepo
    externalAuthorReport openSameObjectBridge openSameObjectBridge
    openSameObjectBridge openSameObjectBridge
    externalAuthorReport externalAuthorReport
