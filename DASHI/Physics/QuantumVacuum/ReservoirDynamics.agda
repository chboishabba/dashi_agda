module DASHI.Physics.QuantumVacuum.ReservoirDynamics where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.QuantumVacuum.PhysicalQuantities as Q

------------------------------------------------------------------------
-- Operational content of Type-I and Type-II machine claims.
-- A cycle cannot be called continuous merely because the apparatus geometry
-- returns to its initial configuration; the supplying reservoir must also be
-- named and its state transition accounted for.
------------------------------------------------------------------------

record ReservoirDynamics : Set₁ where
  constructor mkReservoirDynamics
  field
    State : Set
    available : State → Q.Energy
    extract   : State → State
    replenish : State → State

record TransientExtraction (r : ReservoirDynamics) : Set where
  constructor mkTransientExtraction
  field
    initialState : ReservoirDynamics.State r
    extractedState : ReservoirDynamics.State r
    extractionCloses :
      extractedState ≡ ReservoirDynamics.extract r initialState
    releasedEnergy : Q.Energy
    degradationReceipt : Set

record ContinuousReservoirClosure (r : ReservoirDynamics) : Set where
  constructor mkContinuousReservoirClosure
  field
    initialState : ReservoirDynamics.State r
    afterExtraction : ReservoirDynamics.State r
    afterReplenishment : ReservoirDynamics.State r
    extractionCloses :
      afterExtraction ≡ ReservoirDynamics.extract r initialState
    replenishmentCloses :
      afterReplenishment ≡ ReservoirDynamics.replenish r afterExtraction
    returnsToInitial : afterReplenishment ≡ initialState
    externalSupplyAccounted : Set

-- Returning the apparatus alone is not a reservoir theorem.

record ApparatusResetOnly : Set where
  constructor mkApparatusResetOnly
  field
    ApparatusState : Set
    initial final : ApparatusState
    apparatusReturns : final ≡ initial

apparatusResetDoesNotConstructReservoirClosure :
  ApparatusResetOnly → Set
apparatusResetDoesNotConstructReservoirClosure reset =
  ApparatusResetOnly.ApparatusState reset
