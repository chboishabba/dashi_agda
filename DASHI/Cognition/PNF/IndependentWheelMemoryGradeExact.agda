module DASHI.Cognition.PNF.IndependentWheelMemoryGradeExact where

------------------------------------------------------------------------
-- INDEPENDENT MEMORY PHASE AND DEPTH-WHEEL GRADE
--
-- The older WheelMemoryFibre is an aligned subcarrier: it deliberately
-- realigns MemoryFibre.phase to the C3 depth-wheel ordinal.  This module gives
-- the more general carrier required by the later synthesis: application-level
-- memory phase remains untouched, while a separate proof-bearing wheel
-- coordinate tracks refinement depth.  Alignment is optional evidence.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Physics.Closure.SSPPrimeLane369DepthAddressWheel as Depth
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

record IndependentlyGradedMemory : Set where
  constructor independentlyGradedMemory
  field
    memory : Memory.MemoryFibre
    refinementDepth : Nat
    wheelCoordinate : Depth.WheelDepthCoordinate
    coordinateMatchesDepth :
      wheelCoordinate ≡ Depth.wheelDepthCoordinate refinementDepth

open IndependentlyGradedMemory public

wheelGrade : IndependentlyGradedMemory → Wheel.DepthWheelPhase
wheelGrade state = Depth.residualPhase (wheelCoordinate state)

legacyMemoryPhase : IndependentlyGradedMemory → Nat
legacyMemoryPhase state = Memory.phase (memory state)

attachIndependentWheelGrade :
  Memory.MemoryFibre → Nat → IndependentlyGradedMemory
attachIndependentWheelGrade memory depth =
  independentlyGradedMemory
    memory
    depth
    (Depth.wheelDepthCoordinate depth)
    refl

attachPreservesLegacyMemoryPhase :
  (memory : Memory.MemoryFibre) →
  (depth : Nat) →
  legacyMemoryPhase (attachIndependentWheelGrade memory depth)
  ≡ Memory.phase memory
attachPreservesLegacyMemoryPhase memory depth = refl

record OptionalPhaseAlignment
    (state : IndependentlyGradedMemory) : Set where
  constructor optionalPhaseAlignment
  field
    aligned :
      legacyMemoryPhase state
      ≡ Depth.phaseOrdinal (wheelGrade state)

open OptionalPhaseAlignment public

independentGradeDoesNotRequireAlignment :
  Memory.MemoryFibre → Nat → IndependentlyGradedMemory
independentGradeDoesNotRequireAlignment =
  attachIndependentWheelGrade
