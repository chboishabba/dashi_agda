module DASHI.Physics.Closure.FirstWitnessVacuumBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- First decisive witness / kill-key bridge.
--
-- The Euler sieve exemplar partitions eliminated endpoints by one unique
-- first witness.  This module imports only that structural lesson:
--   * a candidate history may carry one first failing lift;
--   * each failing history is discharged exactly once;
--   * schedule may change the death time while the final quotient is fixed;
--   * competing or contextual witnesses are a separate noncommutative lane.
--
-- This is a bridge carrier, not a proof that physical vacuum constraints are
-- globally commutative or that every history has a unique first witness.


data WitnessDisposition : Set where
  noFailureWitness : WitnessDisposition
  firstFailureAt : Nat → WitnessDisposition
  competingWitnesses : WitnessDisposition
  contextualWitness : WitnessDisposition

witnessDispositionName : WitnessDisposition → String
witnessDispositionName noFailureWitness = "no-failure-witness"
witnessDispositionName (firstFailureAt depth) = "first-failure-at-depth"
witnessDispositionName competingWitnesses = "competing-witnesses"
witnessDispositionName contextualWitness = "contextual-witness"


data EndpointStatus : Set where
  aliveEndpoint : EndpointStatus
  killedEndpoint : EndpointStatus
  undecidedEndpoint : EndpointStatus

endpointStatusName : EndpointStatus → String
endpointStatusName aliveEndpoint = "alive-endpoint"
endpointStatusName killedEndpoint = "killed-endpoint"
endpointStatusName undecidedEndpoint = "undecided-endpoint"

record FirstWitnessRow : Set where
  constructor mkFirstWitnessRow
  field
    rowLabel : String
    disposition : WitnessDisposition
    initialStatus : EndpointStatus
    finalStatus : EndpointStatus
    uniqueFirstWitness : Bool
    irreversibleAfterWitness : Bool
    exactOnceDischarge : Bool
    scheduleMayChangeDeathTime : Bool
    scheduleMayChangeFinalQuotient : Bool
    commutativityClaimed : Bool
    rowStatement : String

open FirstWitnessRow public

survivorRow : FirstWitnessRow
survivorRow =
  mkFirstWitnessRow
    "vacuum-admissible-survivor"
    noFailureWitness
    aliveEndpoint
    aliveEndpoint
    true
    true
    true
    false
    false
    true
    "a candidate with no failing lift survives the checked admissibility tower"

uniqueFailureRow : FirstWitnessRow
uniqueFailureRow =
  mkFirstWitnessRow
    "unique-first-failing-lift"
    (firstFailureAt (suc zero))
    aliveEndpoint
    killedEndpoint
    true
    true
    true
    true
    false
    true
    "a unique first failing lift supports Euler-style exact-once discharge and order-invariant final removal"

competingFailureRow : FirstWitnessRow
competingFailureRow =
  mkFirstWitnessRow
    "competing-failing-lifts"
    competingWitnesses
    undecidedEndpoint
    undecidedEndpoint
    false
    false
    false
    true
    true
    false
    "competing witnesses can change the selected representative and require a noncommutative or amplitude-valued refinement"

contextualFailureRow : FirstWitnessRow
contextualFailureRow =
  mkFirstWitnessRow
    "context-dependent-failing-lift"
    contextualWitness
    undecidedEndpoint
    undecidedEndpoint
    false
    false
    false
    true
    true
    false
    "when the first witness depends on the current field or quotient state, operator order may alter the final representative"

canonicalFirstWitnessRows : List FirstWitnessRow
canonicalFirstWitnessRows =
  survivorRow
  ∷ uniqueFailureRow
  ∷ competingFailureRow
  ∷ contextualFailureRow
  ∷ []

record KillKeyLockReceipt (row : FirstWitnessRow) : Set where
  constructor mkKillKeyLockReceipt
  field
    receiptLabel : String
    receiptRow : FirstWitnessRow
    receiptRowMatches : receiptRow ≡ row
    uniqueWitnessReceipt : uniqueFirstWitness row ≡ true
    irreversibleReceipt : irreversibleAfterWitness row ≡ true
    exactOnceReceipt : exactOnceDischarge row ≡ true
    finalQuotientOrderInvariantReceipt : scheduleMayChangeFinalQuotient row ≡ false
    commutativityReceipt : commutativityClaimed row ≡ true

open KillKeyLockReceipt public

canonicalUniqueFailureKillKeyLock : KillKeyLockReceipt uniqueFailureRow
canonicalUniqueFailureKillKeyLock =
  mkKillKeyLockReceipt
    "canonical-unique-first-witness-kill-key-lock"
    uniqueFailureRow
    refl
    refl
    refl
    refl
    refl
    refl

record VacuumFirstWitnessBoundary : Set where
  constructor mkVacuumFirstWitnessBoundary
  field
    boundaryLabel : String
    rows : List FirstWitnessRow
    uniqueWitnessLaneAvailable : Bool
    competingWitnessLaneExplicit : Bool
    contextualWitnessLaneExplicit : Bool
    universalVacuumCommutativityClaimed : Bool
    vacuumPhysicsDerived : Bool
    boundaryHolds : Bool
    boundaryStatement : String

open VacuumFirstWitnessBoundary public

canonicalVacuumFirstWitnessBoundary : VacuumFirstWitnessBoundary
canonicalVacuumFirstWitnessBoundary =
  mkVacuumFirstWitnessBoundary
    "vacuum-first-witness-boundary"
    canonicalFirstWitnessRows
    true
    true
    true
    false
    false
    true
    "Euler-style commutativity is available only after a unique first-witness partition is supplied; physical vacuum commutativity is not assumed"

canonicalBoundaryDoesNotPromoteUniversalCommutativity :
  universalVacuumCommutativityClaimed canonicalVacuumFirstWitnessBoundary ≡ false
canonicalBoundaryDoesNotPromoteUniversalCommutativity = refl

canonicalBoundaryDoesNotDeriveVacuumPhysics :
  vacuumPhysicsDerived canonicalVacuumFirstWitnessBoundary ≡ false
canonicalBoundaryDoesNotDeriveVacuumPhysics = refl
