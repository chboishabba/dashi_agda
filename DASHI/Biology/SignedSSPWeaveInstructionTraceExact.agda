module DASHI.Biology.SignedSSPWeaveInstructionTraceExact where

------------------------------------------------------------------------
-- INFORMATION-PRESERVING TRACE FOR THE EXISTING SIGNED SSP WEAVE MACHINE
--
-- WeaveEffect intentionally stores only aggregate counts.  That is sufficient
-- for the existing effect theorems, but it forgets the identity of primes
-- introduced by introducePrime / introduceInversePrime.  This module retains
-- the executed instruction trace without changing the scheduler or semantics.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Biology.SignedSSPWeaveProgramMachineExact as Machine

data WeaveTraceEvent : Set where
  builtSixByNineFibreEvent : WeaveTraceEvent
  removedInvariantModeEvent : WeaveTraceEvent
  positivePrimeEvent : Signed.SSPPrime → WeaveTraceEvent
  inversePrimeEvent : Signed.SSPPrime → WeaveTraceEvent
  invariantUnitEvent : WeaveTraceEvent
  refine369Event : WeaveTraceEvent

traceEventOf : Signed.WeaveInstruction → WeaveTraceEvent
traceEventOf Signed.buildSixByNineFibre = builtSixByNineFibreEvent
traceEventOf Signed.removeInvariantMode = removedInvariantModeEvent
traceEventOf (Signed.introducePrime prime) = positivePrimeEvent prime
traceEventOf (Signed.introduceInversePrime prime) = inversePrimeEvent prime
traceEventOf Signed.introduceInvariantUnit = invariantUnitEvent
traceEventOf Signed.refineAt369 = refine369Event

programTrace : List Signed.WeaveInstruction → List WeaveTraceEvent
programTrace [] = []
programTrace (instruction ∷ rest) = traceEventOf instruction ∷ programTrace rest

canonicalVirtualProgramTraceExact :
  programTrace Signed.canonicalVirtualFiftyThreeProgram
  ≡ positivePrimeEvent Signed.ssp59
    ∷ inversePrimeEvent Signed.ssp7
    ∷ invariantUnitEvent
    ∷ []
canonicalVirtualProgramTraceExact = refl

canonicalGeometryProgramTraceExact :
  programTrace Signed.canonicalGeometricFiftyThreeProgram
  ≡ builtSixByNineFibreEvent
    ∷ removedInvariantModeEvent
    ∷ []
canonicalGeometryProgramTraceExact = refl

------------------------------------------------------------------------
-- Executable traced machine.  The trace is stored in reverse execution order
-- so every step is constructor-local and no list append machinery is needed.
------------------------------------------------------------------------

record TracedProgramMachineState : Set where
  constructor traced-program-machine-state
  field
    remainingProgram : List Signed.WeaveInstruction
    accumulatedEffect : Signed.WeaveEffect
    reverseExecutedTrace : List WeaveTraceEvent

open TracedProgramMachineState public

initialTracedProgramMachine :
  List Signed.WeaveInstruction → TracedProgramMachineState
initialTracedProgramMachine program =
  traced-program-machine-state program Signed.emptyWeaveEffect []

stepTracedProgramMachine :
  TracedProgramMachineState → TracedProgramMachineState
stepTracedProgramMachine (traced-program-machine-state [] effect trace) =
  traced-program-machine-state [] effect trace
stepTracedProgramMachine
  (traced-program-machine-state (instruction ∷ rest) effect trace) =
  traced-program-machine-state
    rest
    (Signed.applyInstruction instruction effect)
    (traceEventOf instruction ∷ trace)

runTracedProgramMachine :
  List Signed.WeaveInstruction →
  Signed.WeaveEffect →
  List WeaveTraceEvent →
  TracedProgramMachineState
runTracedProgramMachine [] effect trace =
  traced-program-machine-state [] effect trace
runTracedProgramMachine (instruction ∷ rest) effect trace =
  runTracedProgramMachine
    rest
    (Signed.applyInstruction instruction effect)
    (traceEventOf instruction ∷ trace)

tracedRunEffectAgreesWithExistingExecuteProgram :
  (program : List Signed.WeaveInstruction) →
  (effect : Signed.WeaveEffect) →
  (trace : List WeaveTraceEvent) →
  accumulatedEffect (runTracedProgramMachine program effect trace)
  ≡ Signed.executeProgram program effect
tracedRunEffectAgreesWithExistingExecuteProgram [] effect trace = refl
tracedRunEffectAgreesWithExistingExecuteProgram
  (instruction ∷ rest) effect trace =
  tracedRunEffectAgreesWithExistingExecuteProgram
    rest
    (Signed.applyInstruction instruction effect)
    (traceEventOf instruction ∷ trace)

canonicalVirtualReverseTraceRetainsPrimeIdentity :
  reverseExecutedTrace
    (runTracedProgramMachine
      Signed.canonicalVirtualFiftyThreeProgram
      Signed.emptyWeaveEffect
      [])
  ≡ invariantUnitEvent
    ∷ inversePrimeEvent Signed.ssp7
    ∷ positivePrimeEvent Signed.ssp59
    ∷ []
canonicalVirtualReverseTraceRetainsPrimeIdentity = refl

canonicalGeometryReverseTraceExact :
  reverseExecutedTrace
    (runTracedProgramMachine
      Signed.canonicalGeometricFiftyThreeProgram
      Signed.emptyWeaveEffect
      [])
  ≡ removedInvariantModeEvent
    ∷ builtSixByNineFibreEvent
    ∷ []
canonicalGeometryReverseTraceExact = refl

record SignedSSPWeaveInstructionTraceBoundary : Set where
  constructor signed-ssp-weave-instruction-trace-boundary
  field
    existingInstructionLanguageReused : Bool
    existingApplyInstructionReused : Bool
    primeIdentityRetainedByTrace : Bool
    canonicalVirtualPrime59AndInverse7Retained : Bool
    aggregateEffectStillExactlyExistingEffect : Bool
    genericTraceToRichSummaryProjectionClaimed : Bool

canonicalSignedSSPWeaveInstructionTraceBoundary :
  SignedSSPWeaveInstructionTraceBoundary
canonicalSignedSSPWeaveInstructionTraceBoundary =
  signed-ssp-weave-instruction-trace-boundary
    true true true true true false
