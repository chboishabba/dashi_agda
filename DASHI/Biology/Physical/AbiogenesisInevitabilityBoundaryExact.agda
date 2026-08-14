module DASHI.Biology.Physical.AbiogenesisInevitabilityBoundaryExact where

------------------------------------------------------------------------
-- SOURCE-FACING MOTIVATION
-- Jeremy L. England, "Statistical physics of self-replication",
-- Journal of Chemical Physics 139 (2013), 121923.
-- DOI: 10.1063/1.4818538.
--
-- Sumantra Sarkar and Jeremy L. England,
-- "Design of conditions for self-replication",
-- Physical Review E 100 (2019), 022414.
-- DOI: 10.1103/PhysRevE.100.022414.
--
-- DASHI CONTRIBUTION
-- Exact finite countermodels separating driven persistence, replication,
-- kinetic selection and corrective agency.  None of the lower predicates is
-- silently promoted to an inevitability-of-life theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record CapabilityState : Set where
  constructor capabilityState
  field
    driven : Bool
    persistent : Bool
    selfAmplifying : Bool
    heritableVariation : Bool
    correctiveFeedback : Bool

open CapabilityState public

persistentDrivenNonReplicator : CapabilityState
persistentDrivenNonReplicator =
  capabilityState true true false false false

replicatorWithoutAgency : CapabilityState
replicatorWithoutAgency =
  capabilityState true true true true false

correctiveAgent : CapabilityState
correctiveAgent =
  capabilityState true true true true true

drivenPersistenceDoesNotForceReplication :
  driven persistentDrivenNonReplicator ≡ true
  × persistent persistentDrivenNonReplicator ≡ true
  × selfAmplifying persistentDrivenNonReplicator ≡ false
drivenPersistenceDoesNotForceReplication = refl , (refl , refl)

replicationAndVariationDoNotForceAgency :
  selfAmplifying replicatorWithoutAgency ≡ true
  × heritableVariation replicatorWithoutAgency ≡ true
  × correctiveFeedback replicatorWithoutAgency ≡ false
replicationAndVariationDoNotForceAgency = refl , (refl , refl)

correctiveAgencyAddsCapability : correctiveFeedback correctiveAgent ≡ true
correctiveAgencyAddsCapability = refl

------------------------------------------------------------------------
-- Finite kinetic-selection regression.
------------------------------------------------------------------------

record ReplicatorPopulation : Set where
  constructor replicatorPopulation
  field
    slow fast : Nat

open ReplicatorPopulation public

kineticStep : ReplicatorPopulation → ReplicatorPopulation
kineticStep (replicatorPopulation slow fast) =
  replicatorPopulation (slow + 1) (fast + fast)

initialPopulation : ReplicatorPopulation
initialPopulation = replicatorPopulation 1 1

populationAfterOne : ReplicatorPopulation
populationAfterOne = kineticStep initialPopulation

populationAfterTwo : ReplicatorPopulation
populationAfterTwo = kineticStep populationAfterOne

oneStepCounts :
  slow populationAfterOne ≡ 2 × fast populationAfterOne ≡ 2
oneStepCounts = refl , refl

twoStepFastOutnumbersSlow :
  slow populationAfterTwo < fast populationAfterTwo
twoStepFastOutnumbersSlow = s≤s (s≤s (s≤s z≤n))

------------------------------------------------------------------------
-- Logical boundary: reachability/selection bias is not inevitability.
------------------------------------------------------------------------

record AbiogenesisAuthorityBoundary : Set where
  field
    drivenPersistenceImpliesLife : Bool
    drivenPersistenceImpliesLifeIsFalse :
      drivenPersistenceImpliesLife ≡ false
    replicationImpliesAgency : Bool
    replicationImpliesAgencyIsFalse :
      replicationImpliesAgency ≡ false
    finiteKineticAdvantageProvesAbiogenesisProbabilityOne : Bool
    finiteKineticAdvantageProvesAbiogenesisProbabilityOneIsFalse :
      finiteKineticAdvantageProvesAbiogenesisProbabilityOne ≡ false

canonicalAbiogenesisAuthorityBoundary : AbiogenesisAuthorityBoundary
canonicalAbiogenesisAuthorityBoundary = record
  { drivenPersistenceImpliesLife = false
  ; drivenPersistenceImpliesLifeIsFalse = refl
  ; replicationImpliesAgency = false
  ; replicationImpliesAgencyIsFalse = refl
  ; finiteKineticAdvantageProvesAbiogenesisProbabilityOne = false
  ; finiteKineticAdvantageProvesAbiogenesisProbabilityOneIsFalse = refl
  }
