module DASHI.SexedHistoricalStatisticalExperimentValidation where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.SexedHistoricalStatisticalExperimentHyperfabricExact as Stats
import DASHI.Governance.SexedHistoricalConditionalReversalExact as Reversal
import DASHI.Governance.SexedHistoricalDialecticalOrderHolonomyAnalogueExact as Order
import DASHI.Governance.SexedHistoricalBinaryTernaryDialecticExact as BT
import DASHI.Governance.SexedHistoricalAdaptiveMeasurementRefinementExact as Measure

recordedSexConstructionRegression :
  INF.FactorsThrough Stats.recordedSexSurface Stats.relationalCell → ⊥
recordedSexConstructionRegression =
  Stats.recordedSexCannotRecoverConstructionDirection

constructionPowerRegression :
  INF.FactorsThrough Stats.constructionDirectionSurface Stats.powerContext → ⊥
constructionPowerRegression = Stats.constructionDirectionCannotRecoverPower

associationCausationRegression :
  INF.FactorsThrough Stats.associationSurface Stats.causalStatus → ⊥
associationCausationRegression = Stats.associationCannotRecoverCausalStatus

significanceOutcomeRegression :
  INF.FactorsThrough Stats.significanceSurface Stats.institutionalOutcomeSurface → ⊥
significanceOutcomeRegression = Stats.significanceCannotRecoverInstitutionalOutcome

logisticRoleRegression :
  Stats.dynamicalLogisticMap ≡ Stats.statisticalLogitLink → ⊥
logisticRoleRegression = Stats.dynamicalLogisticRoleIsNotStatisticalLogitRole

recordedSexCompositionRegression :
  INF.FactorsThrough Reversal.recordedSex Reversal.composition → ⊥
recordedSexCompositionRegression =
  Reversal.recordedSexCannotRecoverStratumComposition

conditionalMarginalHighRegression :
  Reversal.withinStratumDirection Reversal.highOpportunityStratum
  ≡ Reversal.pooledDirection → ⊥
conditionalMarginalHighRegression = Reversal.withinHighDiffersFromPooled

conditionalMarginalLowRegression :
  Reversal.withinStratumDirection Reversal.lowOpportunityStratum
  ≡ Reversal.pooledDirection → ⊥
conditionalMarginalLowRegression = Reversal.withinLowDiffersFromPooled

coarseStratumOrderRegression :
  INF.FactorsThrough Order.coarseOrderSurface Order.pathOrder → ⊥
coarseStratumOrderRegression =
  Order.coarseStratumCannotRecoverTransportOrder

dialecticalOrderNoncommutationRegression :
  Order.reinterpretAfterInstitutionalise
  ≡ Order.institutionaliseAfterReinterpret → ⊥
dialecticalOrderNoncommutationRegression = Order.orderDefect

binaryBackwardCollapseRegression :
  INF.FactorsThrough BT.collapseUnresolvedBackward BT.fineHistoricalStatus → ⊥
binaryBackwardCollapseRegression = BT.binaryBackwardCollapseCannotRecoverFineStatus

binaryForwardCollapseRegression :
  INF.FactorsThrough BT.collapseUnresolvedForward BT.fineHistoricalStatus → ⊥
binaryForwardCollapseRegression = BT.binaryForwardCollapseCannotRecoverFineStatus

pathAssessmentRegression :
  INF.FactorsThrough BT.assessPath (λ x → x) → ⊥
pathAssessmentRegression = BT.sameAssessmentDoesNotRecoverOrder

coarsePresentHistoryRegression :
  INF.FactorsThrough Measure.coarsePresent Measure.truePath → ⊥
coarsePresentHistoryRegression = Measure.coarsePresentCannotRecoverHiddenHistory

selectedMeasurementSeparatesRegression :
  Measure.measure
    (Measure.nextMeasurement Measure.recoverPathOrder BT.Suspension.suspendAndRefine)
    Measure.institutionFirstHistory
  ≡ Measure.measure
    (Measure.nextMeasurement Measure.recoverPathOrder BT.Suspension.suspendAndRefine)
    Measure.reinterpretationFirstHistory
  → ⊥
selectedMeasurementSeparatesRegression =
  Measure.selectedPathMeasurementSeparatesCanonicalHistories

canonicalDesignRegression : Stats.SexConstructionStudyDesign
canonicalDesignRegression = Stats.canonicalSexConstructionStudyDesign
