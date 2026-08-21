module DASHI.Biology.EmbodiedHyperformalismRegression where

open import DASHI.Core.Prelude

import DASHI.Biology.MultiscaleAllostaticBodyHyperformalismExact as Multi
import DASHI.Biology.StressPhysiologyCascadeExact as Stress
import DASHI.Biology.ObserverRelativeReachableSubfabricExact as Reach
import DASHI.Biology.BranchStatusAlgebraExact as Status
import DASHI.Biology.TwoBoundaryHyperformalismExact as Two
import DASHI.Biology.TwoBoundaryRepairModesExact as Repair
import DASHI.Biology.EmbodiedBranchingHyperformalismExact as Branch
import DASHI.Biology.EmbodiedHistoryActionFunctionalExact as HistoryCost
import DASHI.Biology.FeltStateSupervoxelExact as Felt
import DASHI.Biology.BodyModulatedEffectiveTopologyExact as Topo
import DASHI.Biology.IntrospectiveHyperformalismIncidenceExact as CV
import DASHI.Biology.BodyModulatedDecisionCoordinatesExact as Controls
import DASHI.Biology.EmbodiedCausalConeFeedbackExact as Cone
import DASHI.Biology.RelationalEmbodiedCoregulationExact as Rel
import DASHI.Biology.EmbodiedHyperformalismSourceRegistry as Sources
import DASHI.Biology.Levin.CrossFrequencyEffectiveTopologyExact as Cross
import DASHI.Core.CubieFaceOrderHolonomyAnalogueExact as CubieOrder

record EmbodiedHyperformalismRegression : Set where
  field
    sixCalibratingSources : Sources.canonicalHyperformalismSourceCount ≡ 6

    sameHPAStillDifferentWholeBody :
      Multi.regulatedStack ≡ Multi.acuteMobilisedStack → ⊥

    acuteCatecholamineAndCortisolTimescalesDiffer :
      Stress.mediatorTimescale Stress.norepinephrine
      ≡ Stress.mediatorTimescale Stress.cortisol → ⊥

    predictedDemandCanChangeRegulatoryBody :
      Multi.applyPolicy (Multi.policyFor Multi.highDemand) Multi.regulatedStack
      ≡ Multi.applyPolicy (Multi.policyFor Multi.lowDemand) Multi.regulatedStack → ⊥

    sameWorldDifferentAccessiblePlan :
      Reach.live Reach.accessibleLayer Reach.regulatedContext Reach.flexiblePlanning
      ≡ Reach.live Reach.accessibleLayer Reach.mobilisedContext Reach.flexiblePlanning
      → ⊥

    predictedWeightDoesNotDetermineAccessibility :
      Status.sameWeightAccessible ≡ Status.sameWeightGated → ⊥

    pruningIsNotReweighting :
      Status.prune Status.baselineBranch ≡ Status.reweight 1 Status.baselineBranch → ⊥

    twoBoundarySectionHasDistinctIntermediateRoutes :
      Two.intermediate Two.threatSection ≡ Two.intermediate Two.safeSection → ⊥

    sameFutureDifferentEmbodiedHistoryChangesSection :
      Two.historyConditionedIntermediate Two.flexibleHistory Two.flexibleSafetyGoal
      ≡ Two.historyConditionedIntermediate Two.threatBiasedHistory Two.flexibleSafetyGoal
      → ⊥

    resourceRepairWidensWithoutHistoryErasure :
      Repair.corridorWidth Repair.contractedCorridor
      ≡ Repair.corridorWidth Repair.resourceRepaired → ⊥

    futureModelRepairWidensWithoutHistoryErasure :
      Repair.corridorWidth Repair.contractedCorridor
      ≡ Repair.corridorWidth Repair.futureModelRepaired → ⊥

    couplingRepairWidensWithoutHistoryErasure :
      Repair.corridorWidth Repair.contractedCorridor
      ≡ Repair.corridorWidth Repair.couplingRepaired → ⊥

    sameWorldGoalHistoryDifferentFeltState :
      Branch.feltState Branch.regulatedBranchState
      ≡ Branch.feltState Branch.mobilisedBranchState → ⊥

    recoveryRetainsHistory :
      Branch.history (Branch.recover Branch.mobilisedBranchState)
      ≡ Branch.history Branch.mobilisedBranchState

    sameBoundariesDifferentTrajectoryCost :
      HistoryCost.totalCost (HistoryCost.costFor HistoryCost.threatRoute)
      ≡ HistoryCost.totalCost (HistoryCost.costFor HistoryCost.safeRoute) → ⊥

    alarmSupervoxelContainsDistinctPhysiology :
      Felt.alarmCubieMobilised ≡ Felt.alarmCubieProlonged → ⊥

    samePhysiologyDifferentPriorChangesFeeling :
      Felt.feltProjection Felt.alarmCubieMobilised
      ≡ Felt.feltProjection Felt.samePhysiologySafetyPrior → ⊥

    sameWaveDifferentBodyChangesEffectiveGate :
      Topo.combinedGate Topo.regulatedTopology Cross.betaLow
      ≡ Topo.combinedGate Topo.mobilisedTopology Cross.betaLow → ⊥

    cvRecoveredTwoDistinctIntermediateRoutes :
      CV.intermediateOf CV.viaS1 ≡ CV.intermediateOf CV.viaS2 → ⊥

    cvRecoveredUpperPath : CV.ObservedPath CV.s0 CV.s3
    cvRecoveredLowerPath : CV.ObservedPath CV.s0 CV.s3

    cvRecoveredContractedOccupancyBottleneck :
      CV.observedFibreCount CV.s0 ≡ CV.observedFibreCount CV.s1 → ⊥

    bodyModulatesMoreThanAccess :
      Controls.decisionThreshold Controls.regulatedControls
      ≡ Controls.decisionThreshold Controls.mobilisedControls → ⊥

    bodyAlsoModulatesMemoryRetrieval :
      Controls.memoryRetrievalGain Controls.regulatedControls
      ≡ Controls.memoryRetrievalGain Controls.mobilisedControls → ⊥

    verticalRegulationPreservesWorld :
      Cone.world (Cone.regulate Cone.mobilisedConstrained)
      ≡ Cone.world Cone.mobilisedConstrained

    horizontalActionCanChangeWorld :
      Cone.world (Cone.act Cone.leaveAction Cone.mobilisedConstrained)
      ≡ Cone.world Cone.mobilisedConstrained → ⊥

    transitionLawCanDeformWithoutDeletingCarrier :
      Cone.gate Cone.baselineLaw Cone.approachSafety
      ≡ Cone.gate Cone.learnedThreatLaw Cone.approachSafety → ⊥

    sameFeelingReportDoesNotRecoverFineCarrier :
      Cone.tenseRegulated ≡ Cone.tenseMobilised → ⊥

    dyadicCalmingCoregulatesBoth :
      Rel.interactionUpdate Rel.calmingSignal Rel.bothMobilised
      ≡ Rel.bothRegulated

    institutionChangesWorldRouteWithoutBodyCoordinate :
      Rel.routeAvailable Rel.closedProcedure Rel.reviewRoute
      ≡ Rel.routeAvailable Rel.openProcedure Rel.reviewRoute → ⊥

    cubieFaceHiddenOrderIsNonfactorable :
      CubieOrder.firstTransport (CubieOrder.secondTransport CubieOrder.root)
      ≡ CubieOrder.secondTransport (CubieOrder.firstTransport CubieOrder.root) → ⊥

open EmbodiedHyperformalismRegression public

canonicalEmbodiedHyperformalismRegression : EmbodiedHyperformalismRegression
canonicalEmbodiedHyperformalismRegression = record
  { sixCalibratingSources = refl
  ; sameHPAStillDifferentWholeBody = Multi.hpaCoordinateDoesNotRecoverWholeBody
  ; acuteCatecholamineAndCortisolTimescalesDiffer =
      Stress.norepinephrineAndCortisolTimescalesDiffer
  ; predictedDemandCanChangeRegulatoryBody =
      Multi.anticipatedDemandCanChangeBodyBeforeDemandObservation
  ; sameWorldDifferentAccessiblePlan =
      Reach.sameWorldButBodyChangesAccessiblePlanning
  ; predictedWeightDoesNotDetermineAccessibility =
      Status.accessibilityStillDiffersAtSameWeight
  ; pruningIsNotReweighting = Status.pruningDiffersFromReweighting
  ; twoBoundarySectionHasDistinctIntermediateRoutes =
      Two.samePastAndFutureAdmitDistinctIntermediateCells
  ; sameFutureDifferentEmbodiedHistoryChangesSection =
      Two.sameFutureDifferentEmbodiedHistoryChangesSection
  ; resourceRepairWidensWithoutHistoryErasure = Repair.resourceRepairWidensCorridor
  ; futureModelRepairWidensWithoutHistoryErasure = Repair.futureModelRepairWidensCorridor
  ; couplingRepairWidensWithoutHistoryErasure = Repair.couplingRepairWidensCorridor
  ; sameWorldGoalHistoryDifferentFeltState =
      Branch.sameWorldGoalHistoryDifferentFeltState
  ; recoveryRetainsHistory =
      Branch.recoveryPreservesHistory Branch.mobilisedBranchState
  ; sameBoundariesDifferentTrajectoryCost = HistoryCost.sameBoundariesDifferentRouteCost
  ; alarmSupervoxelContainsDistinctPhysiology = Felt.sameAlarmDifferentPhysiology
  ; samePhysiologyDifferentPriorChangesFeeling =
      Felt.samePhysiologyDifferentPriorChangesFeltState
  ; sameWaveDifferentBodyChangesEffectiveGate =
      Topo.sameWaveDifferentBodyChangesGate
  ; cvRecoveredTwoDistinctIntermediateRoutes =
      CV.distinctRecoveredIntermediateRoutes
  ; cvRecoveredUpperPath = CV.upperRecoveredPath
  ; cvRecoveredLowerPath = CV.lowerRecoveredPath
  ; cvRecoveredContractedOccupancyBottleneck =
      CV.recoveredContractedBranchIsOccupancyBottleneck
  ; bodyModulatesMoreThanAccess = Controls.thresholdStillDiffers
  ; bodyAlsoModulatesMemoryRetrieval = Controls.memoryRetrievalStillDiffers
  ; verticalRegulationPreservesWorld =
      Cone.verticalRegulationPreservesWorld Cone.mobilisedConstrained
  ; horizontalActionCanChangeWorld = Cone.horizontalLeaveChangesWorld
  ; transitionLawCanDeformWithoutDeletingCarrier =
      Cone.historyDeformationCanCloseApproachWithoutDeletingTransition
  ; sameFeelingReportDoesNotRecoverFineCarrier =
      Cone.sameReportDoesNotRecoverFineCarrier
  ; dyadicCalmingCoregulatesBoth = Rel.calmingCanCoregulateBoth
  ; institutionChangesWorldRouteWithoutBodyCoordinate =
      Rel.procedureChangesWorldReviewRoute
  ; cubieFaceHiddenOrderIsNonfactorable = CubieOrder.orderedEndpointsDiffer
  }
