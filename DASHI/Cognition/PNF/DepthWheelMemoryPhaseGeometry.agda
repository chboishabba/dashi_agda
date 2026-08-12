module DASHI.Cognition.PNF.DepthWheelMemoryPhaseGeometry where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

import Ultrametric as UMetric
import DASHI.Algebra.BalancedTernary as BT
import DASHI.Cognition.PNF.DepthWheelMemoryHyperfabric as MemoryWheel
import DASHI.Cognition.PNF.FibreLearningDynamics as FibreLearning
import DASHI.Cognition.PNF.LearningAlgebra as Learning
import DASHI.Metric.TernaryUltrametric as TernaryMetric
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

------------------------------------------------------------------------
-- Reuse the existing honest three-state ultrametric rather than proving a
-- second copy for the wheel phases.

phaseToTrit : Wheel.DepthWheelPhase → BT.Trit
phaseToTrit Wheel.phase-0 = BT.neg
phaseToTrit Wheel.phase-1 = BT.zero
phaseToTrit Wheel.phase-2 = BT.pos

pulledBackPhaseDistance :
  Wheel.DepthWheelPhase → Wheel.DepthWheelPhase → Agda.Builtin.Nat.Nat
pulledBackPhaseDistance left right =
  TernaryMetric.dT (phaseToTrit left) (phaseToTrit right)

phaseDistanceMatchesMemoryGeometry :
  (left right : Wheel.DepthWheelPhase) →
  pulledBackPhaseDistance left right
  ≡ MemoryWheel.phaseDistance left right
phaseDistanceMatchesMemoryGeometry Wheel.phase-0 Wheel.phase-0 = refl
phaseDistanceMatchesMemoryGeometry Wheel.phase-0 Wheel.phase-1 = refl
phaseDistanceMatchesMemoryGeometry Wheel.phase-0 Wheel.phase-2 = refl
phaseDistanceMatchesMemoryGeometry Wheel.phase-1 Wheel.phase-0 = refl
phaseDistanceMatchesMemoryGeometry Wheel.phase-1 Wheel.phase-1 = refl
phaseDistanceMatchesMemoryGeometry Wheel.phase-1 Wheel.phase-2 = refl
phaseDistanceMatchesMemoryGeometry Wheel.phase-2 Wheel.phase-0 = refl
phaseDistanceMatchesMemoryGeometry Wheel.phase-2 Wheel.phase-1 = refl
phaseDistanceMatchesMemoryGeometry Wheel.phase-2 Wheel.phase-2 = refl

phaseUltrametric : UMetric.Ultrametric Wheel.DepthWheelPhase
phaseUltrametric = record
  { UMetric.Ultrametric.d = pulledBackPhaseDistance
  ; UMetric.Ultrametric.id-zero =
      λ phase → TernaryMetric.id-zeroT (phaseToTrit phase)
  ; UMetric.Ultrametric.symmetric =
      λ left right → TernaryMetric.symT (phaseToTrit left) (phaseToTrit right)
  ; UMetric.Ultrametric.ultratriangle =
      λ left middle right →
        TernaryMetric.ultraT
          (phaseToTrit left)
          (phaseToTrit middle)
          (phaseToTrit right)
  }

------------------------------------------------------------------------
-- Concrete integration with the pre-existing learning receipt and within-fibre
-- transition-graph update surfaces.

reinforcementExistingLearningBridge :
  (source : MemoryWheel.WheelMemoryFibre) →
  String →
  List Learning.WeightedTransition →
  List Learning.WeightedTransition →
  MemoryWheel.ExistingLearningWheelBridge
reinforcementExistingLearningBridge source publicLabel oldGraph newGraph = record
  { MemoryWheel.ExistingLearningWheelBridge.wheelTransition =
      MemoryWheel.reinforcementWheelTransition source
  ; MemoryWheel.ExistingLearningWheelBridge.learningReceipt =
      Learning.reinforcementReceipt (MemoryWheel.memory source)
  ; MemoryWheel.ExistingLearningWheelBridge.fibreUpdate =
      FibreLearning.reweightWithinFibre
        (MemoryWheel.memory source)
        publicLabel
        oldGraph
        newGraph
  ; MemoryWheel.ExistingLearningWheelBridge.receiptBeforeMatchesWheelSource = refl
  ; MemoryWheel.ExistingLearningWheelBridge.receiptAfterMatchesFibreAfter = refl
  ; MemoryWheel.ExistingLearningWheelBridge.fibreRememberedPNFPreserved = refl
  }

extinctionExistingLearningBridge :
  (source : MemoryWheel.WheelMemoryFibre) →
  String →
  List Learning.WeightedTransition →
  List Learning.WeightedTransition →
  MemoryWheel.ExistingLearningWheelBridge
extinctionExistingLearningBridge source publicLabel oldGraph newGraph = record
  { MemoryWheel.ExistingLearningWheelBridge.wheelTransition =
      MemoryWheel.extinctionWheelTransition source
  ; MemoryWheel.ExistingLearningWheelBridge.learningReceipt =
      Learning.extinctionReceipt (MemoryWheel.memory source)
  ; MemoryWheel.ExistingLearningWheelBridge.fibreUpdate =
      FibreLearning.rewireWithinFibre
        (MemoryWheel.memory source)
        publicLabel
        oldGraph
        newGraph
  ; MemoryWheel.ExistingLearningWheelBridge.receiptBeforeMatchesWheelSource = refl
  ; MemoryWheel.ExistingLearningWheelBridge.receiptAfterMatchesFibreAfter = refl
  ; MemoryWheel.ExistingLearningWheelBridge.fibreRememberedPNFPreserved = refl
  }
