module DASHI.SexedHistoricalStatisticalExperimentValidation where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.EpistemicSuspensionExact as Suspension
import DASHI.Core.RelationalHistoryFabricExact as History
import DASHI.Governance.SexedHistoricalStatisticalExperimentHyperfabricExact as Stats
import DASHI.Governance.SexedHistoricalConditionalReversalExact as Reversal
import DASHI.Governance.SexedHistoricalDialecticalOrderHolonomyAnalogueExact as Order
import DASHI.Governance.SexedHistoricalBinaryTernaryDialecticExact as BT
import DASHI.Governance.SexedHistoricalAdaptiveMeasurementRefinementExact as Measure
import DASHI.Governance.SexedHistoricalBase369TransitionPathExact as Path369
import DASHI.Governance.SexedHistoricalBase369AdaptivePathObserverExact as Observe369
import DASHI.Governance.SexedHistoricalEffectiveFibreTransportExact as EffectiveTransport
import DASHI.Governance.SexedHistoricalProductiveDialecticalFibreJoinExact as ProductiveJoin
import DASHI.Governance.SexedHistoricalDialecticalJoinAdaptiveSearchExact as JoinSearch

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
    (Measure.nextMeasurement Measure.recoverPathOrder Suspension.suspendAndRefine)
    Measure.institutionFirstHistory
  ≡ Measure.measure
    (Measure.nextMeasurement Measure.recoverPathOrder Suspension.suspendAndRefine)
    Measure.reinterpretationFirstHistory
  → ⊥
selectedMeasurementSeparatesRegression =
  Measure.selectedPathMeasurementSeparatesCanonicalHistories

base369CrossCountCompositeRegression :
  INF.FactorsThrough Path369.crossCount Path369.compositeChannel → ⊥
base369CrossCountCompositeRegression =
  Path369.coarseCrossCountCannotRecoverComposite

base369CrossOrderRegression :
  Path369.compositeChannel Path369.masculineCrossBack
  ≡ Path369.compositeChannel Path369.feminineCrossBack → ⊥
base369CrossOrderRegression = Path369.crossOrderChangesComposite

base369StratumCompositeRegression :
  INF.FactorsThrough Observe369.compositeStratum Observe369.trueComposite → ⊥
base369StratumCompositeRegression =
  Observe369.base369StratumCannotRecoverComposite

base369EndpointMeasurementRegression :
  Observe369.observe
    (Observe369.nextPathMeasurement
      Observe369.recoverCompositeEndpoint Suspension.suspendAndRefine)
    Observe369.hiddenMasculineCrossBack
  ≡ Observe369.observe
    (Observe369.nextPathMeasurement
      Observe369.recoverCompositeEndpoint Suspension.suspendAndRefine)
    Observe369.hiddenFeminineCrossBack → ⊥
base369EndpointMeasurementRegression =
  Observe369.selectedEndpointMeasurementSeparates

base369SequenceMeasurementRegression :
  Observe369.observe
    (Observe369.nextPathMeasurement
      Observe369.recoverConstructionOrder Suspension.suspendAndRefine)
    Observe369.hiddenMasculineCrossBack
  ≡ Observe369.observe
    (Observe369.nextPathMeasurement
      Observe369.recoverConstructionOrder Suspension.suspendAndRefine)
    Observe369.hiddenFeminineCrossBack → ⊥
base369SequenceMeasurementRegression =
  Observe369.selectedSequenceMeasurementSeparates

formalTransitionLocalReachabilityRegression :
  INF.FactorsThrough
    EffectiveTransport.formalSurface
    EffectiveTransport.reachabilitySurface → ⊥
formalTransitionLocalReachabilityRegression =
  EffectiveTransport.formalTransitionCannotRecoverLocalReachability

samePresentFutureConeRegression :
  INF.FactorsThrough
    (History.observe EffectiveTransport.transportHistoryFabric)
    (History.futureConeOf EffectiveTransport.transportHistoryFabric) → ⊥
samePresentFutureConeRegression =
  EffectiveTransport.sameFormalPresentCannotRecoverFutureCone

productiveJoinRetainsOrderRegression :
  INF.FactorsThrough
    ProductiveJoin.coarseJoin
    ProductiveJoin.joinOrderResidual → ⊥
productiveJoinRetainsOrderRegression =
  ProductiveJoin.productiveJoinDoesNotEraseTransportOrder

joinSearchCoarseProductivityRegression :
  INF.FactorsThrough
    JoinSearch.coarseCandidate
    JoinSearch.expansionStatus → ⊥
joinSearchCoarseProductivityRegression =
  JoinSearch.coarseCandidateCannotRecoverExpansion

joinSearchResidualProductivityRegression :
  INF.FactorsThrough
    JoinSearch.residualStatus
    JoinSearch.expansionStatus → ⊥
joinSearchResidualProductivityRegression =
  JoinSearch.residualAloneCannotRecoverProductivity

joinSearchSelectedProbeRegression :
  JoinSearch.measure
    (JoinSearch.nextJoinMeasurement
      JoinSearch.verifyStrictAffordanceExpansion Suspension.suspendAndRefine)
    JoinSearch.residualPreservingNoExpansion
  ≡ JoinSearch.measure
    (JoinSearch.nextJoinMeasurement
      JoinSearch.verifyStrictAffordanceExpansion Suspension.suspendAndRefine)
    JoinSearch.productiveRelationalJoin → ⊥
joinSearchSelectedProbeRegression =
  JoinSearch.selectedProductivityProbeSeparatesCanonicalCandidates

canonicalProductiveJoinRegression : ProductiveJoin.ProductiveDialecticalJoin
canonicalProductiveJoinRegression = ProductiveJoin.canonicalProductiveJoin

canonicalDesignRegression : Stats.SexConstructionStudyDesign
canonicalDesignRegression = Stats.canonicalSexConstructionStudyDesign
