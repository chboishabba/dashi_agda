module DASHI.Core.ConsumerFibreRefinementSchedulerExact where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerIndexedTrajectoryFibreAdequacyExact as Fibre

------------------------------------------------------------------------
-- CONSUMER FIBRE REFINEMENT SCHEDULER
--
-- Given a consumer whose answer does not descend through the current observer,
-- applications identify the first missing coordinate/producer needed to refine
-- the observation.  This is deliberately generic: the coordinate may be
-- history, provenance, liquidity, authority, incidence, mechanism, etc.
------------------------------------------------------------------------

record RefinementSchedule
    (system : Fibre.ConsumerIndexedFibreSystem) : Set₁ where
  constructor refinementSchedule
  field
    MissingCoordinate Producer : Set
    missingCoordinateFor : Fibre.Consumer system → MissingCoordinate
    producerFor : MissingCoordinate → Producer

open RefinementSchedule public

record ConsumerRefinementResidual
    {system : Fibre.ConsumerIndexedFibreSystem}
    (schedule : RefinementSchedule system)
    (consumer : Fibre.Consumer system) : Set₁ where
  constructor consumerRefinementResidual
  field
    defect : Fibre.ConsumerAdequacyDefect system consumer
    missingCoordinate : MissingCoordinate schedule
    coordinateIsScheduled :
      missingCoordinate ≡ missingCoordinateFor schedule consumer
    producer : Producer schedule
    producerIsScheduled :
      producer ≡ producerFor schedule missingCoordinate

open ConsumerRefinementResidual public

record RefinementClosure
    {system : Fibre.ConsumerIndexedFibreSystem}
    (schedule : RefinementSchedule system)
    (consumer : Fibre.Consumer system) : Set₁ where
  constructor refinementClosure
  field
    residual : ConsumerRefinementResidual schedule consumer
    refinedReceipt : Fibre.ConsumerRefinementReceipt system consumer

open RefinementClosure public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data DefectImpliesUniqueMissingCoordinatePermission : Set where

data MissingCoordinateImpliesProducerInhabitedPermission : Set where

data ScheduledProducerImpliesRefinementClosedPermission : Set where

data OneConsumerRefinementClosesAllConsumersPermission : Set where

defectDoesNotAutoPromoteToUniqueMissingCoordinate :
  DefectImpliesUniqueMissingCoordinatePermission → ⊥
defectDoesNotAutoPromoteToUniqueMissingCoordinate ()

missingCoordinateDoesNotAutoPromoteToProducerInhabited :
  MissingCoordinateImpliesProducerInhabitedPermission → ⊥
missingCoordinateDoesNotAutoPromoteToProducerInhabited ()

scheduledProducerDoesNotAutoPromoteToRefinementClosed :
  ScheduledProducerImpliesRefinementClosedPermission → ⊥
scheduledProducerDoesNotAutoPromoteToRefinementClosed ()

oneConsumerRefinementDoesNotAutoPromoteToAllConsumers :
  OneConsumerRefinementClosesAllConsumersPermission → ⊥
oneConsumerRefinementDoesNotAutoPromoteToAllConsumers ()

record ConsumerFibreRefinementSchedulerBoundary : Set where
  constructor consumerFibreRefinementSchedulerBoundary
  field
    adequacyDefectCanScheduleRefinementWork : Bool
    missingCoordinateMustBeApplicationSupplied : Bool
    scheduledProducerAutomaticallyExists : Bool
    oneConsumerClosureImpliesAllConsumersClosed : Bool

canonicalConsumerFibreRefinementSchedulerBoundary :
  ConsumerFibreRefinementSchedulerBoundary
canonicalConsumerFibreRefinementSchedulerBoundary =
  consumerFibreRefinementSchedulerBoundary true true false false
