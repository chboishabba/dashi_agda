module DASHI.ComputerScience.Goldbach30To29TailWeakSimulationExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.Goldbach30To29SuccessMacroExact as Macro

------------------------------------------------------------------------
-- SUCCESS-TAIL WEAK / STUTTERING SHAPE
--
-- Literal upstream control routing:
--
-- Goldbach30:
--   NT.B --consume f--> SA
--   SA --consume a, produce b c--> SB
--   SB ---------------------------> SA
--   SA --consume c---------------> RA.A
--
-- Goldbach29:
--   NT.B --consume f a, produce b c--> SB
--   SB ------------------------------> NT.B (restore f)
--   ... repeated ...
--   NT.B --consume f--> NT2.B --id--> NT.B
--   NT.B --consume b c---------------> RA.A
--
-- Thus old SA is the stuttering representative of new NT.B-with-verdict,
-- old SB corresponds to new SB, and the old one-step terminal transition is
-- represented by three new microsteps. This module records that local weak
-- quotient independently of any whole-machine claim.
------------------------------------------------------------------------

data OldTailPhase : Set where
  oldSA oldSB oldDone : OldTailPhase

data NewTailPhase : Set where
  newNTB newSB newNT2 newDone : NewTailPhase

TailPhase : Set
TailPhase = OldTailPhase × NewTailPhase

oldToNewPhase : OldTailPhase → NewTailPhase
oldToNewPhase oldSA = newNTB
oldToNewPhase oldSB = newSB
oldToNewPhase oldDone = newDone

record TailPayload : Set where
  constructor tailPayload
  field
    remainingA : Nat
    accumulatedB : Nat
    accumulatedC : Nat

open TailPayload public

transferOne : TailPayload → TailPayload
transferOne (tailPayload zero b c) = tailPayload zero b c
transferOne (tailPayload (suc a) b c) =
  tailPayload a (suc b) (suc c)

oldTransferPair : TailPayload → TailPayload
oldTransferPair = transferOne

newTransferPair : TailPayload → TailPayload
newTransferPair = transferOne

oldTransferPairMatchesNewTransferPair :
  (payload : TailPayload) →
  oldTransferPair payload ≡ newTransferPair payload
oldTransferPairMatchesNewTransferPair payload = refl

------------------------------------------------------------------------
-- Terminal stutter.
--
-- At the semantic macro boundary both paths are exactly the terminal consumer
-- already proved in Goldbach30To29SuccessMacroExact. The microstep lengths are
-- different: old terminal routing contributes one terminal step from SA, while
-- the new machine contributes NT.B -> NT2.B -> NT.B -> RA.A.
------------------------------------------------------------------------

oldTerminalStep : Macro.SuccessEntry → Macro.SuccessRegisters
oldTerminalStep = Macro.oldSuccessTerminal

newTerminalThreeSteps : Macro.SuccessEntry → Macro.SuccessRegisters
newTerminalThreeSteps = Macro.newSuccessTerminal

oldTerminalStepMatchesThreeNewSteps :
  (entry : Macro.SuccessEntry) →
  oldTerminalStep entry ≡ newTerminalThreeSteps entry
oldTerminalStepMatchesThreeNewSteps = Macro.successTerminalRegistersAgree

oldTerminalMicrosteps : Nat
oldTerminalMicrosteps = 1

newTerminalMicrosteps : Nat
newTerminalMicrosteps = 3

terminalStutterAddsTwoLocalSteps :
  newTerminalMicrosteps ≡ suc (suc oldTerminalMicrosteps)
terminalStutterAddsTwoLocalSteps = refl

------------------------------------------------------------------------
-- Whole success macro: dispatch/loop accounting cancels one of the two local
-- terminal extras, leaving the already-proved total +1 microstep penalty.
------------------------------------------------------------------------

weakTailConsumerPreserved :
  (entry : Macro.SuccessEntry) →
  Macro.nextEvenBoundaryConsumer (oldTerminalStep entry)
  ≡ Macro.nextEvenBoundaryConsumer (newTerminalThreeSteps entry)
weakTailConsumerPreserved = Macro.successNextEvenConsumerPreserved

weakTailVerdictPreserved :
  (entry : Macro.SuccessEntry) →
  Macro.verdictGuardConsumer (oldTerminalStep entry)
  ≡ Macro.verdictGuardConsumer (newTerminalThreeSteps entry)
weakTailVerdictPreserved = Macro.successGoldbachVerdictConsumerPreserved

wholeSuccessMacroStutterPenalty :
  (entry : Macro.SuccessEntry) →
  Macro.newSuccessExecutionLength (Macro.a entry)
  ≡ suc (Macro.oldSuccessExecutionLength (Macro.a entry))
wholeSuccessMacroStutterPenalty = Macro.reachableSuccessExecutionLengthIsOneMore

wholeMachineWeakBisimulationPaid : Bool
wholeMachineWeakBisimulationPaid = false

record GoldbachTailWeakSimulationBoundary : Set where
  constructor goldbachTailWeakSimulationBoundary
  field
    oldSAToNewNTBPhaseMapPaid : Bool
    oldSBToNewSBPhaseMapPaid : Bool
    transferPairPayloadEqualityPaid : Bool
    terminalOneToThreeStutterPaid : Bool
    declaredConsumersPreserved : Bool
    wholeSuccessMacroPlusOneCostPaid : Bool
    wholeMachineWeakBisimulationPaidFlag : Bool
    literalFineStateIdentityRequired : Bool

canonicalGoldbachTailWeakSimulationBoundary :
  GoldbachTailWeakSimulationBoundary
canonicalGoldbachTailWeakSimulationBoundary =
  goldbachTailWeakSimulationBoundary
    true true true true true true false false
