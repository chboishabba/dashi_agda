module DASHI.Physics.Plasma.MHDInvariantElsasserFrontierExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- CURRENT SCIENCE FRONTIER AFTER LITERAL PROJECTED-FOURIER CLOSURE
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
    literalPlusCyclicCancellationOwnedIsTrue : literalPlusCyclicCancellationOwned ≡ true

    literalMinusCyclicCancellationOwned : Bool
    literalMinusCyclicCancellationOwnedIsTrue : literalMinusCyclicCancellationOwned ≡ true

    pressureProjectionCancellationOwned : Bool
    pressureProjectionCancellationOwnedIsTrue : pressureProjectionCancellationOwned ≡ true

    totalEnergyTriadConservationOwned : Bool
    totalEnergyTriadConservationOwnedIsTrue : totalEnergyTriadConservationOwned ≡ true

    crossHelicityTriadConservationOwned : Bool
    crossHelicityTriadConservationOwnedIsTrue : crossHelicityTriadConservationOwned ≡ true

    magneticHelicityUsesDistinctHelicalWeight : Bool
    magneticHelicityUsesDistinctHelicalWeightIsTrue : magneticHelicityUsesDistinctHelicalWeight ≡ true

    magneticVectorPotentialObserverOwned : Bool
    magneticVectorPotentialObserverOwnedIsTrue :
      magneticVectorPotentialObserverOwned ≡ true

    physicalInverseCurlObserverOwned : Bool
    physicalInverseCurlObserverOwnedIsTrue : physicalInverseCurlObserverOwned ≡ true

    physicalInverseCurlRealityOwned : Bool
    physicalInverseCurlRealityOwnedIsTrue : physicalInverseCurlRealityOwned ≡ true

    magneticHelicityPlusInverseRadiusWeightOwned : Bool
    magneticHelicityPlusInverseRadiusWeightOwnedIsTrue :
      magneticHelicityPlusInverseRadiusWeightOwned ≡ true

    magneticHelicityMinusInverseRadiusWeightOwned : Bool
    magneticHelicityMinusInverseRadiusWeightOwnedIsTrue :
      magneticHelicityMinusInverseRadiusWeightOwned ≡ true

    inverseCurlSelfAdjointOnTransverseOwned : Bool
    inverseCurlSelfAdjointOnTransverseOwnedIsTrue :
      inverseCurlSelfAdjointOnTransverseOwned ≡ true

    magneticHelicityDirectionalVariationOwned : Bool
    magneticHelicityDirectionalVariationOwnedIsTrue :
      magneticHelicityDirectionalVariationOwned ≡ true

    doubledMagneticFibreOwned : Bool
    doubledMagneticFibreOwnedIsTrue : doubledMagneticFibreOwned ≡ true

    doubledMagneticRealityAndTransverseOwned : Bool
    doubledMagneticRealityAndTransverseOwnedIsTrue :
      doubledMagneticRealityAndTransverseOwned ≡ true

    doubledInductionRealityAndTransverseOwned : Bool
    doubledInductionRealityAndTransverseOwnedIsTrue :
      doubledInductionRealityAndTransverseOwned ≡ true

    literalMagneticHelicityThreeLegConsumerOwned : Bool
    literalMagneticHelicityThreeLegConsumerOwnedIsTrue :
      literalMagneticHelicityThreeLegConsumerOwned ≡ true

    magneticHelicityRealityPairedThreeLegCancellationOwned : Bool
    magneticHelicityRealityPairedThreeLegCancellationOwnedIsFalse :
      magneticHelicityRealityPairedThreeLegCancellationOwned ≡ false

canonicalMHDInvariantElsasserFrontier : MHDInvariantElsasserFrontier
canonicalMHDInvariantElsasserFrontier =
  mhd-invariant-elsasser-frontier
    true refl true refl true refl true refl true refl
    true refl true refl true refl true refl true refl
    true refl true refl true refl true refl
    true refl true refl true refl true refl
    true refl true refl true refl true refl
    true refl true refl true refl true refl
    false refl
