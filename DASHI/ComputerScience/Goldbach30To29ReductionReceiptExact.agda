module DASHI.ComputerScience.Goldbach30To29ReductionReceiptExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.Goldbach29Signed369VendorBridgeExact as Bridge
import DASHI.ComputerScience.Goldbach30To29VendoredSourceAttachmentExact as Source
import DASHI.ComputerScience.Goldbach30To29SuccessMacroExact as Macro
import DASHI.ComputerScience.Goldbach30To29TailWeakSimulationExact as Tail
import DASHI.ComputerScience.Goldbach30To29CheckpointMachineExact as Checkpoint
import DASHI.ComputerScience.Goldbach29ExternalHaltingSemanticsExact as Semantics
import DASHI.ComputerScience.Goldbach30HaltingSourceAuditExact as Audit30
import DASHI.ComputerScience.Goldbach30To29HaltingConsumerCompilerExact as Halting
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed

------------------------------------------------------------------------
-- CONSUMER-RELATIVE MACHINE-REDUCTION RECEIPT
--
-- Four currencies are deliberately kept separate:
--   1. exact upstream source-object identity;
--   2. DASHI-native abstract/checkpoint theorems;
--   3. executable source-driven replay evidence;
--   4. cross-prover / upstream kernel theorem authority.
--
-- Paying one never silently pays another.
------------------------------------------------------------------------

externalGoldbach30ControlStateCount : Nat
externalGoldbach30ControlStateCount = 11

externalGoldbach29ControlStateCount : Nat
externalGoldbach29ControlStateCount = 10

commonRulePrefixCount : Nat
commonRulePrefixCount = 25

fractionCountDeltaPaid :
  suc Bridge.externalGoldbach29FractionCount
  ≡ Bridge.externalGoldbach30FractionCount
fractionCountDeltaPaid = Bridge.externalReductionSavesOneFraction

controlStateDeltaPaid :
  suc externalGoldbach29ControlStateCount
  ≡ externalGoldbach30ControlStateCount
controlStateDeltaPaid = refl

successConsumerPreservationPaid :
  (x : Macro.SuccessEntry) →
  Macro.oldSuccessTerminal x ≡ Macro.newSuccessTerminal x
successConsumerPreservationPaid = Macro.successTerminalRegistersAgree

successExecutionPenaltyPaid :
  (a : Nat) →
  Macro.newSuccessExecutionLength a
  ≡ suc (Macro.oldSuccessExecutionLength a)
successExecutionPenaltyPaid = Macro.newSuccessExecutionLengthIsOneMore

checkpointHaltingEquivalenceTheorem :
  (kernel : Checkpoint.SharedSearchKernel) →
  (start : Checkpoint.TopCheckpoint) →
  Halting.LogicalIff
    (Checkpoint.oldCheckpointHalts kernel start)
    (Checkpoint.newCheckpointHalts kernel start)
checkpointHaltingEquivalenceTheorem =
  Checkpoint.oldCheckpointHaltsIffNewCheckpointHalts

programLengthAndExecutionLengthRemainDifferentConsumers :
  Signed.shortestProgramLengthEqualsExecutionLength
    Signed.canonicalSignedSSPWeaveBoundary
  ≡ false
programLengthAndExecutionLengthRemainDifferentConsumers =
  Signed.shortestProgramLengthEqualsExecutionLengthIsFalse
    Signed.canonicalSignedSSPWeaveBoundary

exactProgramSourceObjectsVendored : Bool
exactProgramSourceObjectsVendored = Source.exactProgramSourceObjectsVendored

sourceDrivenFractranReplayAvailable : Bool
sourceDrivenFractranReplayAvailable = Source.sourceDrivenFractranReplayAvailable

tailWeakSimulationPaid : Bool
tailWeakSimulationPaid = true

externalGoldbach29HaltingSemanticsSourcePaid : Bool
externalGoldbach29HaltingSemanticsSourcePaid =
  Semantics.externalGoldbach29HaltingSemanticsSourcePaid

externalGoldbach29SemanticBuildAuthorityPaid : Bool
externalGoldbach29SemanticBuildAuthorityPaid =
  Semantics.externalGoldbach29SemanticTreeBuildAuthorityPaid

goldbach30NarrativeHaltingClaimFound : Bool
goldbach30NarrativeHaltingClaimFound =
  Audit30.goldbach30NarrativeHaltingClaimFound

goldbach30FormalHaltingSourceFound : Bool
goldbach30FormalHaltingSourceFound =
  Audit30.goldbach30FormalHaltingSourceFound

sameCounterexampleHaltingCompilerPaid : Bool
sameCounterexampleHaltingCompilerPaid = true

checkpointHaltingEquivalencePaid : Bool
checkpointHaltingEquivalencePaid = true

sourceConcreteFractranAttachmentPaid : Bool
sourceConcreteFractranAttachmentPaid =
  Checkpoint.sourceConcreteFractranAttachmentPaid

crossProverProofTransportPaid : Bool
crossProverProofTransportPaid = Source.crossProverProofTransportPaid

------------------------------------------------------------------------
-- Paid Pareto / semantic cut.
--
-- Relative to Goldbach30, Goldbach29 simultaneously has one fewer fraction,
-- one fewer control state, the same guard-corrected success consumer, and one
-- MORE microstep on each success macro. The local tail quotient now explicitly
-- identifies old SA with new NT.B-with-verdict, old SB with new SB, and the old
-- one-step terminal transition with the new three-step terminal stutter.
--
-- The exact Program.lean bytes are now vendored with their upstream Git blob
-- identities, and the replay reads those bytes directly. That pays source-object
-- identity and strong executable evidence. It does NOT manufacture Lean proof
-- transport into Agda.
--
-- Goldbach29's pinned semantic tree contains theorem text, but Main.lean and
-- Loops.lean are the same self-importing blob. Therefore build-verified formal
-- authority is fail-closed. Goldbach30 has only the signed narrative claim for
-- the missing Main/Loops theorem source.
------------------------------------------------------------------------

record Goldbach30To29ReductionReceipt : Set where
  constructor goldbach30To29ReductionReceipt
  field
    upstreamPairPinnedAtSameCommit : Bool
    exactProgramSourceObjectsVendoredFlag : Bool
    commonPrefixTwentyFiveRules : Bool
    fractionCountThirtyToTwentyNine : Bool
    controlStatesElevenToTen : Bool
    saStateEliminated : Bool
    reachableSuccessGuardCorrected : Bool
    successConsumerPreservationPaidFlag : Bool
    successExecutionPenaltyPaidFlag : Bool
    tailWeakSimulationPaidFlag : Bool
    programLengthEqualsExecutionLength : Bool
    sourceDrivenFractranReplayAvailableFlag : Bool
    externalGoldbach29HaltingSemanticsSourcePaidFlag : Bool
    externalGoldbach29SemanticBuildAuthorityPaidFlag : Bool
    goldbach30NarrativeHaltingClaimFoundFlag : Bool
    goldbach30FormalHaltingSourceFoundFlag : Bool
    sameCounterexampleHaltingCompilerPaidFlag : Bool
    checkpointHaltingEquivalencePaidFlag : Bool
    sourceConcreteFractranAttachmentPaidFlag : Bool
    crossProverProofTransportPaidFlag : Bool
    agdaGoldbach29HaltingSemanticsPaidFlag : Bool
    goldbach30HaltingAttachmentPaidFlag : Bool
    wholeMachineReachableWeakBisimulationPaidFlag : Bool
    wholeMachineHaltingEquivalencePaidFlag : Bool
    goldbachConjectureProvedFlag : Bool

open Goldbach30To29ReductionReceipt public

canonicalGoldbach30To29ReductionReceipt : Goldbach30To29ReductionReceipt
canonicalGoldbach30To29ReductionReceipt =
  goldbach30To29ReductionReceipt
    true true true true true true
    true true true true false true
    true false true false true true
    false false false false false false false

wholeMachineReachableWeakBisimulationPaid : Bool
wholeMachineReachableWeakBisimulationPaid = false

-- Reserved for SAME-OBJECT concrete-program halting equivalence, not the
-- checkpoint theorem or executable replay.
wholeMachineHaltingEquivalencePaid : Bool
wholeMachineHaltingEquivalencePaid = false

goldbach30HaltingAttachmentPaid : Bool
goldbach30HaltingAttachmentPaid = Halting.goldbach30HaltingAttachmentPaid

------------------------------------------------------------------------
-- Terminal max-cut status.
------------------------------------------------------------------------

record Goldbach30To29TerminalMaxCut : Set where
  constructor goldbach30To29TerminalMaxCut
  field
    exactUpstreamPairProvenancePaid : Bool
    exactProgramSourceObjectsVendoredTerminalFlag : Bool
    exactStaticReductionPaid : Bool
    reachableSuccessGuardCorrectedTerminalFlag : Bool
    exactSuccessMacroConsumerEqualityPaid : Bool
    exactSuccessMacroCostDeltaPaid : Bool
    localTailWeakSimulationPaid : Bool
    signed369StaticDynamicSeparationReused : Bool
    sourceDrivenReplayPaid : Bool
    checkpointHaltingEquivalencePaidTerminalFlag : Bool
    checkpointConcreteSourceAttachmentPaid : Bool
    goldbach29TheoremTextPresent : Bool
    goldbach29SemanticBuildAuthorityPaid : Bool
    goldbach30NarrativeHaltingClaimFoundTerminalFlag : Bool
    goldbach30FormalHaltingSourceFoundTerminalFlag : Bool
    sameCounterexampleHaltingCompilerPaidTerminalFlag : Bool
    crossProverProofTransportPaidTerminalFlag : Bool
    weakBisimulationRequiredForCheckpointHalting : Bool
    wholeMachineWeakBisimulationPaidTerminalFlag : Bool
    goldbachConjectureProvedTerminalFlag : Bool

canonicalGoldbach30To29TerminalMaxCut : Goldbach30To29TerminalMaxCut
canonicalGoldbach30To29TerminalMaxCut =
  goldbach30To29TerminalMaxCut
    true true true true true true true true true true
    false true false true false true false false false false
