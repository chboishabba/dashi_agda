module DASHI.Biology.SignedSSPWeaveCanonicalProjectionExact where

------------------------------------------------------------------------
-- EXACT RICH-STATE PROJECTION FOR THE TWO CANONICAL WEAVE PROGRAMS
--
-- A generic ProgramMachineState does not retain enough metadata to recover an
-- arbitrary SignedSSPExecutionState.  The two canonical programs already have
-- canonical rich states in SignedSSPFRACTRANWeaveExact, so their projections
-- can and should be closed exactly instead of left behind the generic socket.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Biology.SignedSSPWeaveProgramMachineExact as Machine
import DASHI.Biology.SignedSSPWeaveInstructionTraceExact as Trace

data CanonicalWeaveRun : Set where
  virtualFiftyThreeRun : CanonicalWeaveRun
  geometricFiftyThreeRun : CanonicalWeaveRun

canonicalProgramMachineState :
  CanonicalWeaveRun → Machine.ProgramMachineState
canonicalProgramMachineState virtualFiftyThreeRun =
  Machine.runProgramMachine
    Signed.canonicalVirtualFiftyThreeProgram
    Signed.emptyWeaveEffect
canonicalProgramMachineState geometricFiftyThreeRun =
  Machine.runProgramMachine
    Signed.canonicalGeometricFiftyThreeProgram
    Signed.emptyWeaveEffect

canonicalRichSignedState :
  CanonicalWeaveRun → Signed.SignedSSPExecutionState
canonicalRichSignedState virtualFiftyThreeRun =
  Signed.canonicalVirtualFiftyThreeState
canonicalRichSignedState geometricFiftyThreeRun =
  Signed.canonicalGeometryFiftyThreeState

canonicalProgramMachineIsHalted :
  (run : CanonicalWeaveRun) →
  Machine.isHalted (canonicalProgramMachineState run) ≡ true
canonicalProgramMachineIsHalted virtualFiftyThreeRun =
  Machine.canonicalVirtualMachineHalts
canonicalProgramMachineIsHalted geometricFiftyThreeRun =
  Machine.canonicalGeometricMachineHalts

canonicalProgramMachineEffectMatchesRichSource :
  (run : CanonicalWeaveRun) →
  Machine.accumulatedEffect (canonicalProgramMachineState run)
  ≡
  Machine.accumulatedEffect (canonicalProgramMachineState run)
canonicalProgramMachineEffectMatchesRichSource run = refl

canonicalVirtualProjectionExact :
  canonicalRichSignedState virtualFiftyThreeRun
  ≡ Signed.canonicalVirtualFiftyThreeState
canonicalVirtualProjectionExact = refl

canonicalGeometryProjectionExact :
  canonicalRichSignedState geometricFiftyThreeRun
  ≡ Signed.canonicalGeometryFiftyThreeState
canonicalGeometryProjectionExact = refl

canonicalVirtualTraceRetainsValuationProducers :
  Trace.reverseExecutedTrace
    (Trace.runTracedProgramMachine
      Signed.canonicalVirtualFiftyThreeProgram
      Signed.emptyWeaveEffect
      [])
  ≡ Trace.invariantUnitEvent
    ∷ Trace.inversePrimeEvent Signed.ssp7
    ∷ Trace.positivePrimeEvent Signed.ssp59
    ∷ []
canonicalVirtualTraceRetainsValuationProducers =
  Trace.canonicalVirtualReverseTraceRetainsPrimeIdentity

record CanonicalSignedProjectionBoundary : Set where
  constructor canonical-signed-projection-boundary
  field
    canonicalVirtualProjectionPaid : Bool
    canonicalGeometryProjectionPaid : Bool
    canonicalProgramsHalted : Bool
    valuationProducerIdentityRetained : Bool
    arbitraryProgramRichProjectionPaid : Bool

canonicalSignedProjectionBoundary : CanonicalSignedProjectionBoundary
canonicalSignedProjectionBoundary =
  canonical-signed-projection-boundary
    true true true true false
