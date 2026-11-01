module DASHI.Biology.ConsciousAccessRound2Regression where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)

import DASHI.Biology.QuantitativeCompositionalDefect as Defect
import DASHI.Biology.DynamicEffectiveTopology as Topology
import DASHI.Biology.FiniteCoalitionConstruction as Coalition
import DASHI.Biology.ConsciousAccessRound2SourceAtlas as Sources

record ConsciousAccessRound2Regression : Setω where
  field
    zeroCommutingDefect :
      Defect.triangleDefect Defect.canonicalZeroDefectTriangle ≡ zero

    orderResidualDefectIsOne :
      Defect.triangleDefect Defect.canonicalOrderTriangle ≡ suc zero

    productiveExtensionReducesDefect :
      Defect.netDefect Defect.extendedCoalitionDefects
      ≤
      Defect.netDefect Defect.baseCoalitionDefects

    inhibitedDirectPathClosed :
      Topology.EffectiveEdge Topology.inhibitedState
        Topology.associationNode Topology.planningNode → ⊥

    recurrentDirectPathOpen :
      Topology.EffectiveEdge Topology.recurrentState
        Topology.associationNode Topology.planningNode

    recurrentTwoStepPathOpen :
      Topology.Reachable Topology.recurrentState
        Topology.sensoryNode Topology.planningNode

    selectedCoalitionMinimal :
      (c : Coalition.CoalitionCandidate) →
      Coalition.objective Coalition.selectedCoalition
      ≤
      Coalition.objective c

    selectedCoalitionRecurrent :
      Coalition.coalitionUpdate Coalition.selectedCoalition
      ≡
      Coalition.selectedCoalition

    sourceCountIsFour : Sources.canonicalRound2SourceCount ≡ 4

open ConsciousAccessRound2Regression public

canonicalConsciousAccessRound2Regression : ConsciousAccessRound2Regression
canonicalConsciousAccessRound2Regression =
  record
    { zeroCommutingDefect = Defect.canonicalZeroDefectIsZero
    ; orderResidualDefectIsOne = Defect.canonicalOrderTriangleDefectIsOne
    ; productiveExtensionReducesDefect =
        Defect.productiveExtensionReducesNetDefect
    ; inhibitedDirectPathClosed =
        Topology.inhibitedAssociationPlanningImpossible
    ; recurrentDirectPathOpen =
        Topology.recurrentAssociationPlanning
    ; recurrentTwoStepPathOpen =
        Topology.recurrentSensoryPlanningReach
    ; selectedCoalitionMinimal = Coalition.selectedCoalitionMinimal
    ; selectedCoalitionRecurrent = Coalition.selectedCoalitionIsFixedPoint
    ; sourceCountIsFour = Sources.canonicalRound2SourceCountIsFour
    }
