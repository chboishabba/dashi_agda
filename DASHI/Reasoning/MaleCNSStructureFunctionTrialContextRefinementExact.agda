module DASHI.Reasoning.MaleCNSStructureFunctionTrialContextRefinementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.ConsumerFamilyRefinementKernelExact as Family
import DASHI.Biology.IntersectionalLongitudinalProxyTransitionBridge as Longitudinal

------------------------------------------------------------------------
-- MALECNS STRUCTURE/FUNCTION × TRIAL/CONTEXT REFINEMENT SPECIMEN
--
-- This is an execution-shaped finite specimen, not an empirical Gauthey result.
-- It formalises the first biologically useful consumer pair for the reusable
-- family-refinement kernel: a structure-only code can be adequate for structural
-- identity while failing a joint trial/context functional consumer.  The local
-- repair adds the missing context coordinate and retains the coarse structure.
------------------------------------------------------------------------

data SituatedTrialState : Set where
  discoveryContextState : SituatedTrialState
  replicateContextState : SituatedTrialState

data StructureOnlyCode : Set where
  sharedMaleCNSStructure : StructureOnlyCode

structureOnlyProjection : SituatedTrialState → StructureOnlyCode
structureOnlyProjection discoveryContextState = sharedMaleCNSStructure
structureOnlyProjection replicateContextState = sharedMaleCNSStructure

data TrialContextFunctionalOutcome : Set where
  discoveryFunctionalSignature : TrialContextFunctionalOutcome
  replicateFunctionalSignature : TrialContextFunctionalOutcome

trialContextFunctionalOutcome : SituatedTrialState → TrialContextFunctionalOutcome
trialContextFunctionalOutcome discoveryContextState = discoveryFunctionalSignature
trialContextFunctionalOutcome replicateContextState = replicateFunctionalSignature

trialContextFunctionalOutcomeDiffers :
  trialContextFunctionalOutcome discoveryContextState ≡
  trialContextFunctionalOutcome replicateContextState → ⊥
trialContextFunctionalOutcomeDiffers ()

data StructureTrialConsumer : Set where
  structureIdentityConsumer : StructureTrialConsumer
  trialContextFunctionalConsumer : StructureTrialConsumer

StructureTrialOutcome : StructureTrialConsumer → Set
StructureTrialOutcome structureIdentityConsumer = StructureOnlyCode
StructureTrialOutcome trialContextFunctionalConsumer = TrialContextFunctionalOutcome

structureTrialObservation :
  (consumer : StructureTrialConsumer) →
  SituatedTrialState →
  StructureTrialOutcome consumer
structureTrialObservation structureIdentityConsumer = structureOnlyProjection
structureTrialObservation trialContextFunctionalConsumer = trialContextFunctionalOutcome

structureTrialConsumerFamily :
  Family.ConsumerFamily SituatedTrialState StructureTrialConsumer
structureTrialConsumerFamily =
  Family.consumer-family
    StructureTrialOutcome
    structureTrialObservation

structureOnlyTrialContextWitness :
  NF.NonFactorabilityWitness
    structureOnlyProjection
    trialContextFunctionalOutcome
structureOnlyTrialContextWitness =
  NF.nonFactorabilityWitness
    discoveryContextState
    replicateContextState
    refl
    trialContextFunctionalOutcomeDiffers

structureOnlyTrialContextCollision :
  Family.FamilyCollision
    structureOnlyProjection
    structureTrialConsumerFamily
structureOnlyTrialContextCollision =
  Family.family-collision
    trialContextFunctionalConsumer
    structureOnlyTrialContextWitness

structureOnlyCannotPayJointTrialContextConsumer :
  Family.FamilyFactorsThrough
    structureOnlyProjection
    structureTrialConsumerFamily → ⊥
structureOnlyCannotPayJointTrialContextConsumer =
  Family.collisionRulesOutFamilyFactorisation
    structureOnlyTrialContextCollision

trialContextRechartCannotRecoverFunctionalDifference :
  ∀ {Recharted : Set} →
  (rechart : StructureOnlyCode → Recharted) →
  NF.FactorsThrough
    (λ state → rechart (structureOnlyProjection state))
    trialContextFunctionalOutcome → ⊥
trialContextRechartCannotRecoverFunctionalDifference rechart =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart
    structureOnlyTrialContextWitness

------------------------------------------------------------------------
-- Repair: retain structure and add the missing trial/context distinction.
------------------------------------------------------------------------

data StructureTrialContextCode : Set where
  discoveryStructureContext : StructureTrialContextCode
  replicateStructureContext : StructureTrialContextCode

repairedStructureTrialContextProjection :
  SituatedTrialState → StructureTrialContextCode
repairedStructureTrialContextProjection discoveryContextState =
  discoveryStructureContext
repairedStructureTrialContextProjection replicateContextState =
  replicateStructureContext

recoverStructureOnly : StructureTrialContextCode → StructureOnlyCode
recoverStructureOnly discoveryStructureContext = sharedMaleCNSStructure
recoverStructureOnly replicateStructureContext = sharedMaleCNSStructure

repairedRetainsStructureOnly :
  NF.FactorsThrough
    repairedStructureTrialContextProjection
    structureOnlyProjection
repairedRetainsStructureOnly =
  NF.factorsThrough
    recoverStructureOnly
    (λ
      { discoveryContextState → refl
      ; replicateContextState → refl
      })

interpretTrialContextFunctional :
  StructureTrialContextCode → TrialContextFunctionalOutcome
interpretTrialContextFunctional discoveryStructureContext =
  discoveryFunctionalSignature
interpretTrialContextFunctional replicateStructureContext =
  replicateFunctionalSignature

repairedPaysTrialContextFunctional :
  NF.FactorsThrough
    repairedStructureTrialContextProjection
    trialContextFunctionalOutcome
repairedPaysTrialContextFunctional =
  NF.factorsThrough
    interpretTrialContextFunctional
    (λ
      { discoveryContextState → refl
      ; replicateContextState → refl
      })

structureTrialContextRepair :
  Family.ConsumerFamilyRepair
    structureOnlyProjection
    structureTrialConsumerFamily
    structureOnlyTrialContextCollision
structureTrialContextRepair =
  Family.consumer-family-repair
    StructureTrialContextCode
    repairedStructureTrialContextProjection
    repairedRetainsStructureOnly
    repairedPaysTrialContextFunctional

repairedStructureTrialContextFactorsJointConsumer :
  NF.FactorsThrough
    repairedStructureTrialContextProjection
    trialContextFunctionalOutcome
repairedStructureTrialContextFactorsJointConsumer =
  Family.repairPaysFailedConsumer structureTrialContextRepair

repairedStructureTrialContextRetainsStructure :
  NF.FactorsThrough
    repairedStructureTrialContextProjection
    structureOnlyProjection
repairedStructureTrialContextRetainsStructure =
  Family.repairRetainsCoarseObserver structureTrialContextRepair

interpretRepairedFamily :
  (consumer : StructureTrialConsumer) →
  StructureTrialContextCode →
  StructureTrialOutcome consumer
interpretRepairedFamily structureIdentityConsumer = recoverStructureOnly
interpretRepairedFamily trialContextFunctionalConsumer = interpretTrialContextFunctional

repairedStructureTrialContextPaysWholeFiniteFamily :
  Family.FamilyFactorsThrough
    repairedStructureTrialContextProjection
    structureTrialConsumerFamily
repairedStructureTrialContextPaysWholeFiniteFamily =
  Family.family-factors-through
    interpretRepairedFamily
    (λ
      { structureIdentityConsumer discoveryContextState → refl
      ; structureIdentityConsumer replicateContextState → refl
      ; trialContextFunctionalConsumer discoveryContextState → refl
      ; trialContextFunctionalConsumer replicateContextState → refl
      })

------------------------------------------------------------------------
-- Longitudinal/proxy boundary and empirical firewalls.
------------------------------------------------------------------------

populationTrajectoryStillDoesNotPromoteMechanism :
  Longitudinal.observationMechanismPromoted
    Longitudinal.canonicalPopulationTrajectoryObservation ≡ false
populationTrajectoryStillDoesNotPromoteMechanism =
  Longitudinal.canonicalPopulationTrajectoryDoesNotPromoteMechanism

record MaleCNSStructureFunctionTrialContextBoundary : Set where
  constructor malecns-structure-function-trial-context-boundary
  field
    structureOnlyObserverMayFailTrialContextConsumer : Bool
    structureOnlyObserverMayFailTrialContextConsumerIsTrue :
      structureOnlyObserverMayFailTrialContextConsumer ≡ true

    repairRetainsOriginalStructureObserver : Bool
    repairRetainsOriginalStructureObserverIsTrue :
      repairRetainsOriginalStructureObserver ≡ true

    repairPaysFiniteJointConsumer : Bool
    repairPaysFiniteJointConsumerIsTrue :
      repairPaysFiniteJointConsumer ≡ true

    finiteSpecimenIsNotEmpiricalCrossTrialReplication : Bool
    finiteSpecimenIsNotEmpiricalCrossTrialReplicationIsFalse :
      finiteSpecimenIsNotEmpiricalCrossTrialReplication ≡ false

    empiricalTrialContextCollisionObserved : Bool
    empiricalTrialContextCollisionObservedIsFalse :
      empiricalTrialContextCollisionObserved ≡ false

    independentTrialReplicationPaid : Bool
    independentTrialReplicationPaidIsFalse :
      independentTrialReplicationPaid ≡ false

    contextRefinementEqualsMechanismDiscovery : Bool
    contextRefinementEqualsMechanismDiscoveryIsFalse :
      contextRefinementEqualsMechanismDiscovery ≡ false

    trialContextLabelEqualsAffectSemantics : Bool
    trialContextLabelEqualsAffectSemanticsIsFalse :
      trialContextLabelEqualsAffectSemantics ≡ false

    interpretation : String

open MaleCNSStructureFunctionTrialContextBoundary public

canonicalMaleCNSStructureFunctionTrialContextBoundary :
  MaleCNSStructureFunctionTrialContextBoundary
canonicalMaleCNSStructureFunctionTrialContextBoundary =
  malecns-structure-function-trial-context-boundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "Finite execution template: a structure-only observer can collide for a joint structure/function x trial/context consumer; adding context is a monotone local repair. This does not assert that current Gauthey replicate data already exhibit the collision, does not pay independent replication, and does not promote context into mechanism or affect semantics."
