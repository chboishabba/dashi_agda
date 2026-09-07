module DASHI.Core.ConsumerIndexedTrajectoryFibreAdequacyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.RelationalHistoryFabricExact as History
import DASHI.Core.TrajectoryRecoveryFibreExact as Recovery
import DASHI.Core.SituatedActionabilityFibreExact as Actionability
import DASHI.Core.MultiaxialIncidenceFibreExact as Incidence

------------------------------------------------------------------------
-- CONSUMER-INDEXED TRAJECTORY FIBRE ADEQUACY
--
-- Generic owner for the pattern:
--
--   situated state --observe--> observation fibre
--          |                     |
--          +---- consumer target+
--
-- An observer is adequate only relative to a consumer whose target is constant
-- on every observation fibre.  History, trajectory residue, actionability,
-- recovery, future-cone and incidence are application-supplied target families;
-- this module does not identify those semantics with one another.
------------------------------------------------------------------------

record ConsumerIndexedFibreSystem : Set₁ where
  constructor consumerIndexedFibreSystem
  field
    State Observation Consumer Answer : Set
    observe : State → Observation
    answer : Consumer → State → Answer
    systemReading : String

open ConsumerIndexedFibreSystem public

AdequateForConsumer :
  (system : ConsumerIndexedFibreSystem) → Consumer system → Set₁
AdequateForConsumer system consumer =
  NF.FactorsThrough (observe system) (answer system consumer)

ConsumerAdequacyDefect :
  (system : ConsumerIndexedFibreSystem) → Consumer system → Set
ConsumerAdequacyDefect system consumer =
  NF.NonFactorabilityWitness (observe system) (answer system consumer)

consumerAdequacyDefectBlocksAdequacy :
  ∀ {system : ConsumerIndexedFibreSystem}
    {consumer : Consumer system} →
  ConsumerAdequacyDefect system consumer →
  AdequateForConsumer system consumer →
  ⊥
consumerAdequacyDefectBlocksAdequacy = NF.witnessRulesOutEveryFlatFactorisation

record FibreConstantForConsumer
    (system : ConsumerIndexedFibreSystem)
    (consumer : Consumer system) : Set₁ where
  constructor fibreConstantForConsumer
  field
    decode : Observation system → Answer system
    commutes :
      (state : State system) →
      answer system consumer state ≡ decode (observe system state)

open FibreConstantForConsumer public

fibreConstancyGivesConsumerAdequacy :
  ∀ {system : ConsumerIndexedFibreSystem}
    {consumer : Consumer system} →
  FibreConstantForConsumer system consumer →
  AdequateForConsumer system consumer
fibreConstancyGivesConsumerAdequacy receipt =
  NF.factorsThrough (decode receipt) (commutes receipt)

------------------------------------------------------------------------
-- Same observation / different consumer answer witnesses are the generic
-- fibre-level obstruction.
------------------------------------------------------------------------

record SameObservationDifferentConsumerAnswer
    (system : ConsumerIndexedFibreSystem)
    (consumer : Consumer system) : Set where
  constructor sameObservationDifferentConsumerAnswer
  field
    leftState rightState : State system
    sameObservation : observe system leftState ≡ observe system rightState
    differentAnswer :
      answer system consumer leftState
      ≡ answer system consumer rightState → ⊥

open SameObservationDifferentConsumerAnswer public

sameObservationDifferentAnswerGivesDefect :
  ∀ {system : ConsumerIndexedFibreSystem}
    {consumer : Consumer system} →
  SameObservationDifferentConsumerAnswer system consumer →
  ConsumerAdequacyDefect system consumer
sameObservationDifferentAnswerGivesDefect witness =
  NF.nonFactorabilityWitness
    (leftState witness)
    (rightState witness)
    (sameObservation witness)
    (differentAnswer witness)

------------------------------------------------------------------------
-- Consumer-relative refinement request.
--
-- When a target fails to descend through the current observer, applications may
-- add a missing coordinate.  The generic owner requires an explicit refined
-- observer and a proof that the consumer target descends through it.
------------------------------------------------------------------------

record ConsumerRefinementReceipt
    (system : ConsumerIndexedFibreSystem)
    (consumer : Consumer system) : Set₁ where
  constructor consumerRefinementReceipt
  field
    RefinedObservation : Set
    refine : State system → RefinedObservation
    refinedAnswer : RefinedObservation → Answer system
    preservesCoarseObservation :
      (x y : State system) →
      refine x ≡ refine y → observe system x ≡ observe system y
    targetDescendsAfterRefinement :
      (state : State system) →
      answer system consumer state ≡ refinedAnswer (refine state)

open ConsumerRefinementReceipt public

------------------------------------------------------------------------
-- Multi-consumer adequacy profile.
------------------------------------------------------------------------

record ConsumerAdequacyProfile
    (system : ConsumerIndexedFibreSystem) : Set₁ where
  constructor consumerAdequacyProfile
  field
    Adequate : Consumer system → Set
    adequacySound :
      (consumer : Consumer system) →
      Adequate consumer → AdequateForConsumer system consumer

open ConsumerAdequacyProfile public

record SameObserverDifferentConsumerAdequacy
    (system : ConsumerIndexedFibreSystem) : Set₁ where
  constructor sameObserverDifferentConsumerAdequacy
  field
    adequateConsumer inadequateConsumer : Consumer system
    adequateReceipt : AdequateForConsumer system adequateConsumer
    inadequateDefect : ConsumerAdequacyDefect system inadequateConsumer

open SameObserverDifferentConsumerAdequacy public

------------------------------------------------------------------------
-- Trajectory-aware specialisation surface.
------------------------------------------------------------------------

record TrajectoryConsumerSurface : Set₁ where
  constructor trajectoryConsumerSurface
  field
    State Observation Consumer Answer : Set
    observe : State → Observation
    answer : Consumer → State → Answer
    HistoryCode ResidueCode ActionabilityCode RecoveryCode FutureConeCode IncidenceCode : Set
    historyOf : State → HistoryCode
    residueOf : State → ResidueCode
    actionabilityOf : State → ActionabilityCode
    recoveryOf : State → RecoveryCode
    futureConeOf : State → FutureConeCode
    incidenceOf : State → IncidenceCode
    surfaceReading : String

open TrajectoryConsumerSurface public

asConsumerIndexedSystem : TrajectoryConsumerSurface → ConsumerIndexedFibreSystem
asConsumerIndexedSystem surface =
  consumerIndexedFibreSystem
    (State surface)
    (Observation surface)
    (Consumer surface)
    (Answer surface)
    (observe surface)
    (answer surface)
    (surfaceReading surface)

------------------------------------------------------------------------
-- Exact finite witness: one coarse observation can be adequate for one
-- consumer and inadequate for another.
------------------------------------------------------------------------

data DemoState : Set where
  demoLeft : DemoState
  demoRight : DemoState

data DemoObservation : Set where
  demoSame : DemoObservation

data DemoConsumer : Set where
  coarseConsumer : DemoConsumer
  pathSensitiveConsumer : DemoConsumer

data DemoAnswer : Set where
  coarseAnswer : DemoAnswer
  leftPathAnswer : DemoAnswer
  rightPathAnswer : DemoAnswer

demoObserve : DemoState → DemoObservation
demoObserve _ = demoSame

demoAnswer : DemoConsumer → DemoState → DemoAnswer
demoAnswer coarseConsumer _ = coarseAnswer
demoAnswer pathSensitiveConsumer demoLeft = leftPathAnswer
demoAnswer pathSensitiveConsumer demoRight = rightPathAnswer

demoSystem : ConsumerIndexedFibreSystem
demoSystem =
  consumerIndexedFibreSystem
    DemoState DemoObservation DemoConsumer DemoAnswer
    demoObserve demoAnswer
    "The same coarse observation is adequate for a coarse consumer but not for a path-sensitive consumer."

demoCoarseAdequate : AdequateForConsumer demoSystem coarseConsumer
demoCoarseAdequate =
  NF.factorsThrough (λ _ → coarseAnswer) (λ _ → refl)

demoPathDefect : ConsumerAdequacyDefect demoSystem pathSensitiveConsumer
demoPathDefect =
  NF.nonFactorabilityWitness demoLeft demoRight refl (λ ())

demoSameObserverDifferentConsumerAdequacy :
  SameObserverDifferentConsumerAdequacy demoSystem
demoSameObserverDifferentConsumerAdequacy =
  sameObserverDifferentConsumerAdequacy
    coarseConsumer pathSensitiveConsumer
    demoCoarseAdequate demoPathDefect

------------------------------------------------------------------------
-- Cross-owner boundary witnesses.  These are compatibility references, not
-- semantic collapses.
------------------------------------------------------------------------

queryIndexedBoundary : Query.QueryIndexedProjectionAdequacyBoundary
queryIndexedBoundary = Query.canonicalQueryIndexedProjectionAdequacyBoundary

historyBoundary : History.RelationalHistoryFabricBoundary
historyBoundary = History.canonicalRelationalHistoryFabricBoundary

recoveryBoundary : Recovery.TrajectoryRecoveryFibreBoundary
recoveryBoundary = Recovery.canonicalTrajectoryRecoveryFibreBoundary

actionabilityBoundary : Actionability.SituatedActionabilityFibreBoundary
actionabilityBoundary = Actionability.canonicalSituatedActionabilityFibreBoundary

incidenceBoundary : Incidence.MultiaxialIncidenceFibreBoundary
incidenceBoundary = Incidence.canonicalMultiaxialIncidenceFibreBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ObserverAdequateImpliesAllConsumerAdequacyPermission : Set where

data OneConsumerAdequacyImpliesAnotherConsumerAdequacyPermission : Set where

data SameObservationImpliesSameHistoryPermission : Set where

data SameObservationImpliesSameActionabilityPermission : Set where

data SameObservationImpliesSameRecoveryPermission : Set where

data SameObservationImpliesSameIncidencePermission : Set where

data RefinementImpliesSeparatingStatePermission : Set where

observerAdequateDoesNotAutoPromoteToAllConsumers :
  ObserverAdequateImpliesAllConsumerAdequacyPermission → ⊥
observerAdequateDoesNotAutoPromoteToAllConsumers ()

oneConsumerAdequacyDoesNotAutoPromoteToAnother :
  OneConsumerAdequacyImpliesAnotherConsumerAdequacyPermission → ⊥
oneConsumerAdequacyDoesNotAutoPromoteToAnother ()

sameObservationDoesNotAutoPromoteToSameHistory :
  SameObservationImpliesSameHistoryPermission → ⊥
sameObservationDoesNotAutoPromoteToSameHistory ()

sameObservationDoesNotAutoPromoteToSameActionability :
  SameObservationImpliesSameActionabilityPermission → ⊥
sameObservationDoesNotAutoPromoteToSameActionability ()

sameObservationDoesNotAutoPromoteToSameRecovery :
  SameObservationImpliesSameRecoveryPermission → ⊥
sameObservationDoesNotAutoPromoteToSameRecovery ()

sameObservationDoesNotAutoPromoteToSameIncidence :
  SameObservationImpliesSameIncidencePermission → ⊥
sameObservationDoesNotAutoPromoteToSameIncidence ()

refinementDoesNotAutoPromoteToFullStateSeparation :
  RefinementImpliesSeparatingStatePermission → ⊥
refinementDoesNotAutoPromoteToFullStateSeparation ()

record ConsumerIndexedTrajectoryFibreBoundary : Set where
  constructor consumerIndexedTrajectoryFibreBoundary
  field
    adequacyIsConsumerIndexed : Bool
    fibreCollisionCanRefuteAdequacy : Bool
    oneConsumerAdequacyImpliesAllConsumers : Bool
    refinementMayRestoreSpecificConsumerAdequacy : Bool
    refinementAutomaticallyRecoversFullState : Bool

canonicalConsumerIndexedTrajectoryFibreBoundary :
  ConsumerIndexedTrajectoryFibreBoundary
canonicalConsumerIndexedTrajectoryFibreBoundary =
  consumerIndexedTrajectoryFibreBoundary true true false true false
