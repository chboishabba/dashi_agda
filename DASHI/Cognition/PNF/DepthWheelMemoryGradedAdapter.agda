module DASHI.Cognition.PNF.DepthWheelMemoryGradedAdapter where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Cognition.PNF.DepthWheelMemoryHyperfabric as MemoryWheel
import DASHI.Foundations.DepthWheelGradedDynamics as Graded
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

record MemoryAtGrade (grade : Wheel.DepthWheelPhase) : Set where
  constructor memoryAtGrade
  field
    state : MemoryWheel.WheelMemoryFibre
    stateHasGrade : MemoryWheel.wheelPhase state ≡ grade

open MemoryAtGrade public

advanceAtGrade :
  ∀ {grade} →
  MemoryWheel.MemoryPreservingUpdate →
  MemoryAtGrade grade →
  MemoryAtGrade (Wheel.nextDepthWheelPhase grade)
advanceAtGrade update source =
  memoryAtGrade
    (MemoryWheel.advancePreservingUpdate update (state source))
    (trans
      (MemoryWheel.advanceMovesPhase update (state source))
      (cong Wheel.nextDepthWheelPhase (stateHasGrade source)))

gradedMemoryLearningSystem :
  MemoryWheel.ThreePhaseLearningProgram →
  Graded.GradedDepthWheelSystem
gradedMemoryLearningSystem program =
  Graded.gradedDepthWheelSystem
    MemoryAtGrade
    (advanceAtGrade (MemoryWheel.phase0Update program))
    (advanceAtGrade (MemoryWheel.phase1Update program))
    (advanceAtGrade (MemoryWheel.phase2Update program))

phase0OneWheelUnderlyingState :
  (program : MemoryWheel.ThreePhaseLearningProgram) →
  (source : MemoryAtGrade Wheel.phase-0) →
  state
    (Graded.oneWheelAtPhase0
      (gradedMemoryLearningSystem program)
      source)
  ≡ MemoryWheel.runOneLearningWheel program (state source)
phase0OneWheelUnderlyingState program source = refl
