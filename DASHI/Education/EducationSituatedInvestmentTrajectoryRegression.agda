module DASHI.Education.EducationSituatedInvestmentTrajectoryRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Education.EducationSituatedInvestmentTrajectoryExact as Trajectory
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.LearningAlgebra as Learning
import DASHI.Cognition.PNF.DecisionAutonomyExact as Autonomy
import DASHI.Cognition.PNF.TraumaMemoryHypervoxelBridge as Trauma

sameReturnAutonomyRegression :
  Trajectory.returnObserver Trajectory.sameReturnRevisableLowBurden
  ≡ Trajectory.returnObserver Trajectory.sameReturnConstrainedHighBurden
sameReturnAutonomyRegression = refl

sameReturnStillCannotRecoverAutonomy :
  Trajectory.returnObserver Trajectory.sameReturnRevisableLowBurden
  ≡ Trajectory.returnObserver Trajectory.sameReturnConstrainedHighBurden
sameReturnStillCannotRecoverAutonomy = refl

unmonetisedStillNotZero :
  Trajectory.observedUnmonetised ≡ Trajectory.measuredZero → ⊥
unmonetisedStillNotZero = Trajectory.observedUnmonetisedIsNotMeasuredZero

memoryExtinctionRegression :
  (memory : Memory.MemoryFibre) →
  Memory.rememberedEvent (Memory.extinguishActionDominance memory)
  ≡ Memory.rememberedEvent memory
memoryExtinctionRegression = Trajectory.memoryExtinctionPreservesRememberedEvent

contextTransferRegression :
  (receipt : Learning.ContextGeneralisationReceipt) →
  Learning.generalisationIsAutomatic receipt ≡ Agda.Builtin.Bool.false
contextTransferRegression = Trajectory.contextGeneralisationRemainsNonAutomatic

autonomyOwnerRegression :
  Trajectory.canonicalAutonomyBoundary ≡ Autonomy.canonicalAutonomyBoundary
autonomyOwnerRegression = refl

traumaOwnerRegression :
  Trajectory.canonicalTraumaAuthorityBoundary
  ≡ Trauma.canonicalTraumaMemoryHypervoxelAuthorityBoundary
traumaOwnerRegression = refl
