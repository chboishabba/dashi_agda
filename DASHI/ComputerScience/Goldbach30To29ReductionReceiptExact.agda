module DASHI.ComputerScience.Goldbach30To29ReductionReceiptExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.Goldbach29Signed369VendorBridgeExact as Bridge
import DASHI.ComputerScience.Goldbach30To29SuccessMacroExact as Macro
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed

------------------------------------------------------------------------
-- CONSUMER-RELATIVE MACHINE-REDUCTION RECEIPT
--
-- This is deliberately specialized to the attributed Goldbach30/29 pair.
-- DASHI already owns generic observer/refinement machinery; creating another
-- generic transition calculus here would duplicate it.  The receipt records
-- exactly what is paid on the literal published reduction surface and exactly
-- what remains unpaid.
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

programLengthAndExecutionLengthRemainDifferentConsumers :
  Signed.shortestProgramLengthEqualsExecutionLength
    Signed.canonicalSignedSSPWeaveBoundary
  ≡ false
programLengthAndExecutionLengthRemainDifferentConsumers =
  Signed.shortestProgramLengthEqualsExecutionLengthIsFalse
    Signed.canonicalSignedSSPWeaveBoundary

------------------------------------------------------------------------
-- Paid Pareto point.
--
-- Relative to Goldbach30, Goldbach29 simultaneously has:
--   - one fewer fraction;
--   - one fewer control state;
--   - the same success-macro terminal register consumer;
--   - one MORE microstep on that success macro.
--
-- Thus static machine compression and dynamic execution cost are genuinely
-- distinct coordinates on an actual attributed FRACTRAN reduction.
------------------------------------------------------------------------

record Goldbach30To29ReductionReceipt : Set where
  constructor goldbach30To29ReductionReceipt
  field
    upstreamPairPinnedAtSameCommit : Bool
    commonPrefixTwentyFiveRules : Bool
    fractionCountThirtyToTwentyNine : Bool
    controlStatesElevenToTen : Bool
    saStateEliminated : Bool
    successConsumerPreservationPaidFlag : Bool
    successExecutionPenaltyPaidFlag : Bool
    programLengthEqualsExecutionLength : Bool
    wholeMachineReachableWeakBisimulationPaidFlag : Bool
    wholeMachineHaltingEquivalencePaidFlag : Bool
    conjectureLevelGoldbachSemanticsPaidFlag : Bool

open Goldbach30To29ReductionReceipt public

canonicalGoldbach30To29ReductionReceipt : Goldbach30To29ReductionReceipt
canonicalGoldbach30To29ReductionReceipt =
  goldbach30To29ReductionReceipt
    true true true true true
    true true false
    false false false

wholeMachineReachableWeakBisimulationPaid : Bool
wholeMachineReachableWeakBisimulationPaid = false

wholeMachineHaltingEquivalencePaid : Bool
wholeMachineHaltingEquivalencePaid = false

conjectureLevelGoldbachSemanticsPaid : Bool
conjectureLevelGoldbachSemanticsPaid = false

------------------------------------------------------------------------
-- Terminal max-cut status.
------------------------------------------------------------------------

record Goldbach30To29TerminalMaxCut : Set where
  constructor goldbach30To29TerminalMaxCut
  field
    exactUpstreamPairProvenancePaid : Bool
    exactStaticReductionPaid : Bool
    exactSuccessMacroConsumerEqualityPaid : Bool
    exactSuccessMacroCostDeltaPaid : Bool
    signed369StaticDynamicSeparationReused : Bool
    sharedPrefixRequiresReproof : Bool
    successTailRequiresFurtherMacroProof : Bool
    literalWholeMachineReachabilityRelationRequired : Bool
    literalHaltingConsumerRequired : Bool
    externalGoldbachTheoremAttachmentRequired : Bool

canonicalGoldbach30To29TerminalMaxCut : Goldbach30To29TerminalMaxCut
canonicalGoldbach30To29TerminalMaxCut =
  goldbach30To29TerminalMaxCut
    true true true true true
    false false
    true true true
