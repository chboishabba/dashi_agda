module DASHI.Economics.AIInfrastructureConsumerFibreRefinementSchedulerExact where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerFibreRefinementSchedulerExact as Scheduler
import DASHI.Economics.AIInfrastructureConsumerIndexedFibreAdequacyExact as AI

------------------------------------------------------------------------
-- APPLICATION SCHEDULER
--
-- Converts consumer-specific fibre defects into the next missing coordinate and
-- producer.  This is an adapter to the generic Core scheduler, not a new
-- adequacy calculus.
------------------------------------------------------------------------

data AIProducer : Set where
  refinancingContextProducer
  financingHistoryProducer
  residualAssetValueProducer
  futureOptionalityProducer
  lossIncidenceProducer
  : AIProducer

producerForCoordinate : AI.AIFibreMissingCoordinate → AIProducer
producerForCoordinate AI.refinancingContextCoordinate = refinancingContextProducer
producerForCoordinate AI.financingHistoryCoordinate = financingHistoryProducer
producerForCoordinate AI.residualAssetValueCoordinate = residualAssetValueProducer
producerForCoordinate AI.futureOptionalityCoordinate = futureOptionalityProducer
producerForCoordinate AI.lossIncidenceCoordinate = lossIncidenceProducer

aiRefinementSchedule : Scheduler.RefinementSchedule AI.aiInfrastructureFibreSystem
aiRefinementSchedule = Scheduler.refinementSchedule
  AI.AIFibreMissingCoordinate
  AIProducer
  AI.missingCoordinateFor
  producerForCoordinate

refinancingResidual :
  Scheduler.ConsumerRefinementResidual
    aiRefinementSchedule AI.refinancingConsumer
refinancingResidual = Scheduler.consumerRefinementResidual
  AI.refinancingDefect
  AI.refinancingContextCoordinate
  refl
  refinancingContextProducer
  refl

recoveryResidual :
  Scheduler.ConsumerRefinementResidual
    aiRefinementSchedule AI.capitalRecoveryConsumer
recoveryResidual = Scheduler.consumerRefinementResidual
  AI.recoveryDefect
  AI.financingHistoryCoordinate
  refl
  financingHistoryProducer
  refl

futureResidual :
  Scheduler.ConsumerRefinementResidual
    aiRefinementSchedule AI.futureConeConsumer
futureResidual = Scheduler.consumerRefinementResidual
  AI.futureConeDefect
  AI.futureOptionalityCoordinate
  refl
  futureOptionalityProducer
  refl

incidenceResidual :
  Scheduler.ConsumerRefinementResidual
    aiRefinementSchedule AI.incidenceConsumer
incidenceResidual = Scheduler.consumerRefinementResidual
  AI.incidenceDefect
  AI.lossIncidenceCoordinate
  refl
  lossIncidenceProducer
  refl

------------------------------------------------------------------------
-- Domain translation to our empirical frontier.
------------------------------------------------------------------------

data EmpiricalProducerSurface : Set where
  refinancingSpreadCoverageAndLiquidityPanel
  financingTrajectoryAndWriteDownPanel
  residualRentalValueAndForcedSalePanel
  optionalityAndRecontractingPanel
  creditorEquityPublicAndCommunityIncidencePanel
  : EmpiricalProducerSurface

empiricalProducerFor : AIProducer → EmpiricalProducerSurface
empiricalProducerFor refinancingContextProducer = refinancingSpreadCoverageAndLiquidityPanel
empiricalProducerFor financingHistoryProducer = financingTrajectoryAndWriteDownPanel
empiricalProducerFor residualAssetValueProducer = residualRentalValueAndForcedSalePanel
empiricalProducerFor futureOptionalityProducer = optionalityAndRecontractingPanel
empiricalProducerFor lossIncidenceProducer = creditorEquityPublicAndCommunityIncidencePanel

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ScheduledPanelImpliesDataRecoveredPermission : Set where

data OnePanelClosesAllConsumersPermission : Set where

scheduledPanelDoesNotAutoPromoteToRecoveredData :
  ScheduledPanelImpliesDataRecoveredPermission → ⊥
scheduledPanelDoesNotAutoPromoteToRecoveredData ()

onePanelDoesNotAutoPromoteToAllConsumersClosed :
  OnePanelClosesAllConsumersPermission → ⊥
onePanelDoesNotAutoPromoteToAllConsumersClosed ()
