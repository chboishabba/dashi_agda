module DASHI.Cognition.PNF.SensibLawConsumerSourcePrioritySchedulerBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.BoundAcquisitionDemandExact as Bound
import DASHI.Core.ConsumerIndexedTrajectoryFibreAdequacyExact as Fibre
import DASHI.Core.ConsumerFibreRefinementSchedulerExact as Scheduler
import DASHI.Cognition.PNF.SensibLawConsumerSourceAcquisitionPriorityExact as Priority

------------------------------------------------------------------------
-- CONSUMER-SOURCE PRIORITY <-> EXISTING REFINEMENT SCHEDULER
--
-- The generic refinement scheduler may identify an exact missing coordinate for
-- an exact consumer.  For legal/source acquisition, that scheduled residual is
-- necessary but not sufficient: the coordinate must also be live-sensitive for
-- the selected consumer under a ConsumerSourcePolicy.
------------------------------------------------------------------------

record PrioritySchedulerAlignment
    {system : Fibre.ConsumerIndexedFibreSystem}
    (schedule : Scheduler.RefinementSchedule system)
    (policy : Priority.ConsumerSourcePolicy) : Set₁ where
  constructor priority-scheduler-alignment
  field
    policyConsumerFor : Fibre.Consumer system → Priority.Consumer policy
    policyCoordinateFor :
      Scheduler.MissingCoordinate schedule → Priority.Coordinate policy
    alignmentReference : String

open PrioritySchedulerAlignment public

record SchedulerSourceAdmission
    {system : Fibre.ConsumerIndexedFibreSystem}
    {schedule : Scheduler.RefinementSchedule system}
    {policy : Priority.ConsumerSourcePolicy}
    (alignment : PrioritySchedulerAlignment schedule policy)
    (consumer : Fibre.Consumer system)
    (residual : Scheduler.ConsumerRefinementResidual schedule consumer) : Set₁ where
  constructor scheduler-source-admission
  field
    acquireNowPermission :
      Priority.AcquireNowPermission
        policy
        (policyConsumerFor alignment consumer)
        (policyCoordinateFor alignment (Scheduler.missingCoordinate residual))
    admissionReference : String

open SchedulerSourceAdmission public

------------------------------------------------------------------------
-- Exact bound-demand adapter.
--
-- BoundAcquisitionDemand already proves that an acquisition attacks the exact
-- selected residual and producer.  This wrapper adds the missing legal/source
-- condition: the selected scheduler coordinate is admitted for acquisition NOW
-- for the exact selected consumer.
------------------------------------------------------------------------

record PriorityAdmittedBoundSourceDemand
    {system : Fibre.ConsumerIndexedFibreSystem}
    {schedule : Scheduler.RefinementSchedule system}
    {policy : Priority.ConsumerSourcePolicy}
    (priorityAlignment : PrioritySchedulerAlignment schedule policy)
    (consumer : Fibre.Consumer system)
    (schedulerResidual : Scheduler.ConsumerRefinementResidual schedule consumer)
    {Residual Producer Acquisition : Set}
    (acquisitionAlignment :
      Bound.AcquisitionAlignment
        (Scheduler.MissingCoordinate schedule)
        Residual
        Producer
        Acquisition)
    (liveResidual : Residual) : Set₁ where
  constructor priority-admitted-bound-source-demand
  field
    schedulerAdmission :
      SchedulerSourceAdmission priorityAlignment consumer schedulerResidual
    boundDemand :
      Bound.BoundAcquisitionDemand
        acquisitionAlignment
        (Scheduler.missingCoordinate schedulerResidual)
        liveResidual
    demandReference : String

open PriorityAdmittedBoundSourceDemand public

admittedDemandTargetsScheduledCoordinate :
  ∀ {system schedule policy}
    {priorityAlignment : PrioritySchedulerAlignment schedule policy}
    {consumer : Fibre.Consumer system}
    {schedulerResidual : Scheduler.ConsumerRefinementResidual schedule consumer}
    {Residual Producer Acquisition}
    {acquisitionAlignment :
      Bound.AcquisitionAlignment
        (Scheduler.MissingCoordinate schedule)
        Residual Producer Acquisition}
    {liveResidual : Residual} →
  (demand :
    PriorityAdmittedBoundSourceDemand
      priorityAlignment consumer schedulerResidual acquisitionAlignment liveResidual) →
  Bound.acquisitionResidual acquisitionAlignment
    (Bound.acquisition (boundDemand demand))
  ≡ Bound.residualForRequirement acquisitionAlignment
      (Scheduler.missingCoordinate schedulerResidual)
admittedDemandTargetsScheduledCoordinate demand =
  Bound.acquisitionPaysSelectedResidual (boundDemand demand)

admittedDemandUsesScheduledCoordinateProducer :
  ∀ {system schedule policy}
    {priorityAlignment : PrioritySchedulerAlignment schedule policy}
    {consumer : Fibre.Consumer system}
    {schedulerResidual : Scheduler.ConsumerRefinementResidual schedule consumer}
    {Residual Producer Acquisition}
    {acquisitionAlignment :
      Bound.AcquisitionAlignment
        (Scheduler.MissingCoordinate schedule)
        Residual Producer Acquisition}
    {liveResidual : Residual} →
  (demand :
    PriorityAdmittedBoundSourceDemand
      priorityAlignment consumer schedulerResidual acquisitionAlignment liveResidual) →
  Bound.acquisitionProducer acquisitionAlignment
    (Bound.acquisition (boundDemand demand))
  ≡ Bound.producerForRequirement acquisitionAlignment
      (Scheduler.missingCoordinate schedulerResidual)
admittedDemandUsesScheduledCoordinateProducer demand =
  Bound.acquisitionUsesSelectedProducer (boundDemand demand)

------------------------------------------------------------------------
-- A blocked/deferred coordinate can remain a perfectly real scheduled residual;
-- what is denied is only permission to turn it into the present source-demand
-- work item for this consumer.
------------------------------------------------------------------------

data ScheduledResidualAutomaticallyAdmittedForSourceWork : Set where
data BoundDemandAloneSuppliesAcquireNowPermission : Set where
data CounterfactualSensitivityAutomaticallyAdmitsActualConsumer : Set where
data NoAcquireNowPermissionDeletesScheduledResidual : Set where

scheduledResidualDoesNotAutoAdmitSourceWork :
  ScheduledResidualAutomaticallyAdmittedForSourceWork → ⊥
scheduledResidualDoesNotAutoAdmitSourceWork ()

boundDemandDoesNotSupplyConsumerPriority :
  BoundDemandAloneSuppliesAcquireNowPermission → ⊥
boundDemandDoesNotSupplyConsumerPriority ()

counterfactualDoesNotAutoAdmitActualConsumer :
  CounterfactualSensitivityAutomaticallyAdmitsActualConsumer → ⊥
counterfactualDoesNotAutoAdmitActualConsumer ()

noPermissionDoesNotDeleteResidual :
  NoAcquireNowPermissionDeletesScheduledResidual → ⊥
noPermissionDoesNotDeleteResidual ()

record ConsumerSourcePrioritySchedulerBridgeBoundary : Set where
  constructor consumer-source-priority-scheduler-bridge-boundary
  field
    schedulerResidualStillRequired : Bool
    acquireNowPermissionSeparatelyRequired : Bool
    boundDemandStillRequired : Bool
    boundDemandAloneEstablishesConsumerPriority : Bool
    blockedCoordinateMayRemainScheduled : Bool

canonicalConsumerSourcePrioritySchedulerBridgeBoundary :
  ConsumerSourcePrioritySchedulerBridgeBoundary
canonicalConsumerSourcePrioritySchedulerBridgeBoundary =
  consumer-source-priority-scheduler-bridge-boundary
    true true true false true
