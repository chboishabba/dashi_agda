module DASHI.Physics.Plasma.MHDInvariantElsasserFrontierExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- CURRENT SCIENCE FRONTIER
------------------------------------------------------------------------

record MHDInvariantElsasserFrontier : Set where
  constructor mhd-invariant-elsasser-frontier
  field
    energyCoordinateRechartOwned : Bool
    energyCoordinateRechartOwnedIsTrue : energyCoordinateRechartOwned ≡ true

    crossHelicityCoordinateRechartOwned : Bool
    crossHelicityCoordinateRechartOwnedIsTrue : crossHelicityCoordinateRechartOwned ≡ true

    tangentRechartOwned : Bool
    tangentRechartOwnedIsTrue : tangentRechartOwned ≡ true

    energyDirectionalVariationRechartOwned : Bool
    energyDirectionalVariationRechartOwnedIsTrue : energyDirectionalVariationRechartOwned ≡ true

    crossHelicityDirectionalVariationRechartOwned : Bool
    crossHelicityDirectionalVariationRechartOwnedIsTrue : crossHelicityDirectionalVariationRechartOwned ≡ true

    literalPlusCyclicCancellationOwned : Bool
    literalPlusCyclicCancellationOwnedIsFalse : literalPlusCyclicCancellationOwned ≡ false

    literalMinusCyclicCancellationOwned : Bool
    literalMinusCyclicCancellationOwnedIsFalse : literalMinusCyclicCancellationOwned ≡ false

    pressureProjectionCancellationOwned : Bool
    pressureProjectionCancellationOwnedIsFalse : pressureProjectionCancellationOwned ≡ false

    totalEnergyTriadConservationOwned : Bool
    totalEnergyTriadConservationOwnedIsFalse : totalEnergyTriadConservationOwned ≡ false

    crossHelicityTriadConservationOwned : Bool
    crossHelicityTriadConservationOwnedIsFalse : crossHelicityTriadConservationOwned ≡ false

    magneticHelicityUsesDistinctHelicalWeight : Bool
    magneticHelicityUsesDistinctHelicalWeightIsTrue : magneticHelicityUsesDistinctHelicalWeight ≡ true

    magneticHelicityWeightedCyclicCancellationOwned : Bool
    magneticHelicityWeightedCyclicCancellationOwnedIsFalse : magneticHelicityWeightedCyclicCancellationOwned ≡ false

canonicalMHDInvariantElsasserFrontier : MHDInvariantElsasserFrontier
canonicalMHDInvariantElsasserFrontier =
  mhd-invariant-elsasser-frontier
    true refl true refl true refl true refl true refl
    false refl false refl false refl false refl false refl
    true refl false refl
