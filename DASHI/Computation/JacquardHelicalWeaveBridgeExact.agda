module DASHI.Computation.JacquardHelicalWeaveBridgeExact where

open import DASHI.Core.Prelude

import Data.Fin as Fin
import DASHI.Computation.JacquardOperationalSemanticsExact as Jacquard
import DASHI.Topology.HelicalWeaveMappingTorusExact as Helix

------------------------------------------------------------------------
-- Concrete bridge from helical C3 phase to a three-warp Jacquard program.
-- Each row lifts exactly the warp selected by the current phase; the next row
-- rotates the selection.  The generated three-row program therefore executes
-- one complete helical phase orbit and compiler correctness applies directly.
------------------------------------------------------------------------

warp0 : Fin.Fin 3
warp0 = Fin.zero

warp1 : Fin.Fin 3
warp1 = Fin.suc Fin.zero

warp2 : Fin.Fin 3
warp2 = Fin.suc (Fin.suc Fin.zero)

phaseLiftMask : Helix.Phase3 → Jacquard.LiftMask 3
phaseLiftMask Helix.phase0 Fin.zero = true
phaseLiftMask Helix.phase0 (Fin.suc Fin.zero) = false
phaseLiftMask Helix.phase0 (Fin.suc (Fin.suc Fin.zero)) = false
phaseLiftMask Helix.phase1 Fin.zero = false
phaseLiftMask Helix.phase1 (Fin.suc Fin.zero) = true
phaseLiftMask Helix.phase1 (Fin.suc (Fin.suc Fin.zero)) = false
phaseLiftMask Helix.phase2 Fin.zero = false
phaseLiftMask Helix.phase2 (Fin.suc Fin.zero) = false
phaseLiftMask Helix.phase2 (Fin.suc (Fin.suc Fin.zero)) = true

helicalJacquardProgram :
  Helix.Phase3 →
  Jacquard.JacquardProgram 3
helicalJacquardProgram phase =
  Jacquard.liftMask (phaseLiftMask phase)
  ∷ Jacquard.liftMask (phaseLiftMask (Helix.rotatePhase phase))
  ∷ Jacquard.liftMask
      (phaseLiftMask (Helix.rotatePhase (Helix.rotatePhase phase)))
  ∷ []

helicalJacquardSchedule :
  Helix.Phase3 →
  Jacquard.LiftSchedule 3
helicalJacquardSchedule phase =
  phaseLiftMask phase
  ∷ phaseLiftMask (Helix.rotatePhase phase)
  ∷ phaseLiftMask (Helix.rotatePhase (Helix.rotatePhase phase))
  ∷ []

compileHelicalProgram :
  (phase : Helix.Phase3) →
  Jacquard.compile (helicalJacquardProgram phase)
  ≡ helicalJacquardSchedule phase
compileHelicalProgram Helix.phase0 = refl
compileHelicalProgram Helix.phase1 = refl
compileHelicalProgram Helix.phase2 = refl

executeCompiledHelicalProgram :
  (phase : Helix.Phase3) →
  Jacquard.executeSchedule
    (Jacquard.compile (helicalJacquardProgram phase))
  ≡ Jacquard.executeProgram (helicalJacquardProgram phase)
executeCompiledHelicalProgram phase =
  Jacquard.compilePreservesExecution (helicalJacquardProgram phase)

phase0Warp0CrossingWord :
  Jacquard.crossingWordAt warp0
    (Jacquard.executeProgram (helicalJacquardProgram Helix.phase0))
  ≡ Jacquard.warpOver ∷ Jacquard.weftOver ∷ Jacquard.weftOver ∷ []
phase0Warp0CrossingWord = refl

phase0Warp1CrossingWord :
  Jacquard.crossingWordAt warp1
    (Jacquard.executeProgram (helicalJacquardProgram Helix.phase0))
  ≡ Jacquard.weftOver ∷ Jacquard.warpOver ∷ Jacquard.weftOver ∷ []
phase0Warp1CrossingWord = refl

phase0Warp2CrossingWord :
  Jacquard.crossingWordAt warp2
    (Jacquard.executeProgram (helicalJacquardProgram Helix.phase0))
  ≡ Jacquard.weftOver ∷ Jacquard.weftOver ∷ Jacquard.warpOver ∷ []
phase0Warp2CrossingWord = refl

rotatingStartPhasePermutesRows :
  Jacquard.executeProgram (helicalJacquardProgram Helix.phase1)
  ≡ Jacquard.weaveRow (phaseLiftMask Helix.phase1)
    ∷ Jacquard.weaveRow (phaseLiftMask Helix.phase2)
    ∷ Jacquard.weaveRow (phaseLiftMask Helix.phase0)
    ∷ []
rotatingStartPhasePermutesRows = refl

record JacquardHelicalBridgeBoundary : Set where
  constructor jacquardHelicalBridgeBoundary
  field
    compiledScheduleExact :
      (phase : Helix.Phase3) →
      Jacquard.compile (helicalJacquardProgram phase)
      ≡ helicalJacquardSchedule phase
    compilerExecutionExact :
      (phase : Helix.Phase3) →
      Jacquard.executeSchedule
        (Jacquard.compile (helicalJacquardProgram phase))
      ≡ Jacquard.executeProgram (helicalJacquardProgram phase)
    threeWarpScheduleIsPhysicalCircularKnittingMachine : Bool
    threeWarpScheduleIsPhysicalCircularKnittingMachineIsFalse :
      threeWarpScheduleIsPhysicalCircularKnittingMachine ≡ false

canonicalJacquardHelicalBridgeBoundary :
  JacquardHelicalBridgeBoundary
canonicalJacquardHelicalBridgeBoundary =
  jacquardHelicalBridgeBoundary
    compileHelicalProgram
    executeCompiledHelicalProgram
    false refl
