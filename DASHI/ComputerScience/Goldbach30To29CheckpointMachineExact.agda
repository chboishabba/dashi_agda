module DASHI.ComputerScience.Goldbach30To29CheckpointMachineExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.Goldbach30To29SuccessMacroExact as Macro
import DASHI.ComputerScience.Goldbach30To29HaltingConsumerCompilerExact as Halting

------------------------------------------------------------------------
-- CHECKPOINT-MACHINE EQUIVALENCE
--
-- The two published abstract machines share the primality-test and failure
-- machinery; their only reduction-relevant difference is the success tail.
-- `SharedSearchKernel` therefore leaves the shared classifier/failure path
-- application-supplied and plugs in DASHI's exact, guard-corrected success
-- macros on the two sides.
--
-- This gives a theorem stronger than a bounded replay: for EVERY supplied
-- shared search kernel, every finite checkpoint trace is identical and the two
-- checkpoint machines have equivalent halting witnesses.
--
-- Attribution firewall: this module is a DASHI-native reconstruction at the
-- checkpoint interface.  It does not silently identify these Agda functions
-- with Mike Dupont's concrete Lean `astep`/FRACTRAN values.  That same-object
-- cross-prover attachment remains a separate receipt obligation.
------------------------------------------------------------------------

record TopCheckpoint : Set where
  constructor topCheckpoint
  field
    -- Actual a is `suc aTail`; this matches the success contract and keeps the
    -- top-of-search tested left summand structurally positive.
    aTail : Nat
    b : Nat
    c : Nat

open TopCheckpoint public

actualA : TopCheckpoint → Nat
actualA top = suc (aTail top)

data CheckpointOutcome : Set where
  halted : CheckpointOutcome
  running : TopCheckpoint → CheckpointOutcome

------------------------------------------------------------------------
-- Shared search kernel.
--
-- `isSuccessfulSplit` represents the result of the shared primality-test
-- engine.  `failureStep` represents the shared composite/exhaustion branch,
-- including the possibility of halting when no split remains.
------------------------------------------------------------------------

record SharedSearchKernel : Set where
  constructor sharedSearchKernel
  field
    isSuccessfulSplit : TopCheckpoint → Bool
    failureStep : TopCheckpoint → CheckpointOutcome

open SharedSearchKernel public

successEntryAtCheckpoint : TopCheckpoint → Macro.SuccessEntry
successEntryAtCheckpoint top =
  -- The checkpoint success boundary is clean: f=1 and s=g=0 are structural in
  -- Macro.SuccessEntry; d=e=h=m=0 are the source-reachable top-loop values.
  Macro.successEntry
    (aTail top)
    (b top)
    (c top)
    0 0 0 0

terminalCheckpoint : Macro.SuccessRegisters → TopCheckpoint
terminalCheckpoint registers =
  -- Both success macros return a=2, hence aTail=1 at the next checkpoint.
  topCheckpoint
    1
    (Macro.regB registers)
    (Macro.regC registers)

oldSuccessCheckpoint : TopCheckpoint → TopCheckpoint
oldSuccessCheckpoint top =
  terminalCheckpoint
    (Macro.oldSuccessTerminal (successEntryAtCheckpoint top))

newSuccessCheckpoint : TopCheckpoint → TopCheckpoint
newSuccessCheckpoint top =
  terminalCheckpoint
    (Macro.newSuccessTerminal (successEntryAtCheckpoint top))

successCheckpointAgree :
  (top : TopCheckpoint) →
  oldSuccessCheckpoint top ≡ newSuccessCheckpoint top
successCheckpointAgree top =
  cong terminalCheckpoint
    (Macro.successTerminalRegistersAgree (successEntryAtCheckpoint top))

------------------------------------------------------------------------
-- One checkpoint step.
------------------------------------------------------------------------

oldCheckpointStep : SharedSearchKernel → TopCheckpoint → CheckpointOutcome
oldCheckpointStep kernel top with isSuccessfulSplit kernel top
... | true = running (oldSuccessCheckpoint top)
... | false = failureStep kernel top

newCheckpointStep : SharedSearchKernel → TopCheckpoint → CheckpointOutcome
newCheckpointStep kernel top with isSuccessfulSplit kernel top
... | true = running (newSuccessCheckpoint top)
... | false = failureStep kernel top

checkpointStepAgree :
  (kernel : SharedSearchKernel) →
  (top : TopCheckpoint) →
  oldCheckpointStep kernel top ≡ newCheckpointStep kernel top
checkpointStepAgree kernel top with isSuccessfulSplit kernel top
... | true = cong running (successCheckpointAgree top)
... | false = refl

------------------------------------------------------------------------
-- Every finite checkpoint trace agrees.
------------------------------------------------------------------------

runCheckpoint :
  Nat →
  (TopCheckpoint → CheckpointOutcome) →
  TopCheckpoint →
  CheckpointOutcome
runCheckpoint zero step top = running top
runCheckpoint (suc fuel) step top with step top
... | halted = halted
... | running next = runCheckpoint fuel step next

oldCheckpointRun :
  SharedSearchKernel → Nat → TopCheckpoint → CheckpointOutcome
oldCheckpointRun kernel fuel top =
  runCheckpoint fuel (oldCheckpointStep kernel) top

newCheckpointRun :
  SharedSearchKernel → Nat → TopCheckpoint → CheckpointOutcome
newCheckpointRun kernel fuel top =
  runCheckpoint fuel (newCheckpointStep kernel) top

checkpointRunsAgree :
  (kernel : SharedSearchKernel) →
  (fuel : Nat) →
  (top : TopCheckpoint) →
  oldCheckpointRun kernel fuel top
  ≡
  newCheckpointRun kernel fuel top
checkpointRunsAgree kernel zero top = refl
checkpointRunsAgree kernel (suc fuel) top
  with isSuccessfulSplit kernel top
... | true rewrite successCheckpointAgree top =
  checkpointRunsAgree kernel fuel (newSuccessCheckpoint top)
... | false with failureStep kernel top
...   | halted = refl
...   | running next = checkpointRunsAgree kernel fuel next

------------------------------------------------------------------------
-- Halting equivalence at the checkpoint machine.
------------------------------------------------------------------------

record CheckpointHalts
    (step : TopCheckpoint → CheckpointOutcome)
    (start : TopCheckpoint) : Set where
  constructor checkpointHalts
  field
    fuel : Nat
    haltsAt : runCheckpoint fuel step start ≡ halted

open CheckpointHalts public

oldCheckpointHalts :
  SharedSearchKernel → TopCheckpoint → Set
oldCheckpointHalts kernel start =
  CheckpointHalts (oldCheckpointStep kernel) start

newCheckpointHalts :
  SharedSearchKernel → TopCheckpoint → Set
newCheckpointHalts kernel start =
  CheckpointHalts (newCheckpointStep kernel) start

oldCheckpointHaltsImpliesNewCheckpointHalts :
  (kernel : SharedSearchKernel) →
  (start : TopCheckpoint) →
  oldCheckpointHalts kernel start →
  newCheckpointHalts kernel start
oldCheckpointHaltsImpliesNewCheckpointHalts kernel start witness =
  checkpointHalts
    (fuel witness)
    (trans
      (sym (checkpointRunsAgree kernel (fuel witness) start))
      (haltsAt witness))

newCheckpointHaltsImpliesOldCheckpointHalts :
  (kernel : SharedSearchKernel) →
  (start : TopCheckpoint) →
  newCheckpointHalts kernel start →
  oldCheckpointHalts kernel start
newCheckpointHaltsImpliesOldCheckpointHalts kernel start witness =
  checkpointHalts
    (fuel witness)
    (trans
      (checkpointRunsAgree kernel (fuel witness) start)
      (haltsAt witness))

oldCheckpointHaltsIffNewCheckpointHalts :
  (kernel : SharedSearchKernel) →
  (start : TopCheckpoint) →
  Halting.LogicalIff
    (oldCheckpointHalts kernel start)
    (newCheckpointHalts kernel start)
oldCheckpointHaltsIffNewCheckpointHalts kernel start =
  Halting.logicalIff
    (oldCheckpointHaltsImpliesNewCheckpointHalts kernel start)
    (newCheckpointHaltsImpliesOldCheckpointHalts kernel start)

------------------------------------------------------------------------
-- Concrete first-success regression at the checkpoint interface.
------------------------------------------------------------------------

firstGoldbachCheckpoint : TopCheckpoint
firstGoldbachCheckpoint = topCheckpoint 1 2 0

firstSuccessCheckpointAgreement :
  oldSuccessCheckpoint firstGoldbachCheckpoint
  ≡ topCheckpoint 1 4 1
firstSuccessCheckpointAgreement = refl

firstSuccessCheckpointAgreement29 :
  newSuccessCheckpoint firstGoldbachCheckpoint
  ≡ topCheckpoint 1 4 1
firstSuccessCheckpointAgreement29 = refl

------------------------------------------------------------------------
-- Boundary / authority receipt.
------------------------------------------------------------------------

sourceConcreteFractranAttachmentPaid : Bool
sourceConcreteFractranAttachmentPaid = false

record GoldbachCheckpointEquivalenceBoundary : Set where
  constructor goldbachCheckpointEquivalenceBoundary
  field
    reachableSuccessGuardCorrected : Bool
    sharedClassifierAndFailureAreParametric : Bool
    successCheckpointEqualityPaid : Bool
    allFiniteCheckpointTracesEqual : Bool
    checkpointHaltingEquivalencePaid : Bool
    literalFineStateBisimulationRequiredForCheckpointHalting : Bool
    sourceConcreteFractranAttachmentPaidFlag : Bool
    goldbachConjectureProved : Bool

canonicalGoldbachCheckpointEquivalenceBoundary :
  GoldbachCheckpointEquivalenceBoundary
canonicalGoldbachCheckpointEquivalenceBoundary =
  goldbachCheckpointEquivalenceBoundary
    true true true true true false false false
