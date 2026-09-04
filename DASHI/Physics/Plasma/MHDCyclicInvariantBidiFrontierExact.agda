module DASHI.Physics.Plasma.MHDCyclicInvariantBidiFrontierExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- CYCLIC INVARIANT FRONTIER AFTER LITERAL REPO-MODEL CLOSURE
------------------------------------------------------------------------

record MHDCyclicInvariantBidiFrontier : Set where
  constructor mhd-cyclic-invariant-bidi-frontier
  field
    genericSkewPairCancellationOwned : Bool
    genericSkewPairCancellationOwnedIsTrue :
      genericSkewPairCancellationOwned ≡ true

    nsMhdPreNormTheoremShapeBridgeOwned : Bool
    nsMhdPreNormTheoremShapeBridgeOwnedIsTrue :
      nsMhdPreNormTheoremShapeBridgeOwned ≡ true

    couplingExchangeAntisymmetryShapeOwned : Bool
    couplingExchangeAntisymmetryShapeOwnedIsTrue :
      couplingExchangeAntisymmetryShapeOwned ≡ true

    transverseLerayRemovalOwned : Bool
    transverseLerayRemovalOwnedIsTrue : transverseLerayRemovalOwned ≡ true

    hermitianConjugatePayloadExchangeOwned : Bool
    hermitianConjugatePayloadExchangeOwnedIsTrue :
      hermitianConjugatePayloadExchangeOwned ≡ true

    derivativeFactorAntisymmetryReuseOwned : Bool
    derivativeFactorAntisymmetryReuseOwnedIsTrue :
      derivativeFactorAntisymmetryReuseOwned ≡ true

    twoFieldOrderedRealityPairCancellationOwned : Bool
    twoFieldOrderedRealityPairCancellationOwnedIsTrue :
      twoFieldOrderedRealityPairCancellationOwned ≡ true

    twoFieldThreeLegNormalFormCancellationOwned : Bool
    twoFieldThreeLegNormalFormCancellationOwnedIsTrue :
      twoFieldThreeLegNormalFormCancellationOwned ≡ true

    literalProjectedElsasserInteractionOwned : Bool
    literalProjectedElsasserInteractionOwnedIsTrue :
      literalProjectedElsasserInteractionOwned ≡ true

    projectedInteractionNormalFormReductionOwned : Bool
    projectedInteractionNormalFormReductionOwnedIsTrue :
      projectedInteractionNormalFormReductionOwned ≡ true

    projectedThreeLegCancellationOwned : Bool
    projectedThreeLegCancellationOwnedIsTrue :
      projectedThreeLegCancellationOwned ≡ true

    plusProjectedPseudoEnergyCancellationOwned : Bool
    plusProjectedPseudoEnergyCancellationOwnedIsTrue :
      plusProjectedPseudoEnergyCancellationOwned ≡ true

    minusProjectedPseudoEnergyCancellationOwned : Bool
    minusProjectedPseudoEnergyCancellationOwnedIsTrue :
      minusProjectedPseudoEnergyCancellationOwned ≡ true

    literalRepoIdealElsasserGalerkinDynamicsOwned : Bool
    literalRepoIdealElsasserGalerkinDynamicsOwnedIsTrue :
      literalRepoIdealElsasserGalerkinDynamicsOwned ≡ true

    repoGalerkinToProjectedInteractionWeldOwned : Bool
    repoGalerkinToProjectedInteractionWeldOwnedIsTrue :
      repoGalerkinToProjectedInteractionWeldOwned ≡ true

    totalEnergyLiteralRepoTriadConservationOwned : Bool
    totalEnergyLiteralRepoTriadConservationOwnedIsTrue :
      totalEnergyLiteralRepoTriadConservationOwned ≡ true

    crossHelicityLiteralRepoTriadConservationOwned : Bool
    crossHelicityLiteralRepoTriadConservationOwnedIsTrue :
      crossHelicityLiteralRepoTriadConservationOwned ≡ true

    sourcePdeProjectedFourierBidiWeldSocketOwned : Bool
    sourcePdeProjectedFourierBidiWeldSocketOwnedIsTrue :
      sourcePdeProjectedFourierBidiWeldSocketOwned ≡ true

    externalSourcePdeToRepoProjectedFourierWeldOwned : Bool
    externalSourcePdeToRepoProjectedFourierWeldOwnedIsFalse :
      externalSourcePdeToRepoProjectedFourierWeldOwned ≡ false

    magneticHelicityClosedByEnergyCrossHelicityCompiler : Bool
    magneticHelicityClosedByEnergyCrossHelicityCompilerIsFalse :
      magneticHelicityClosedByEnergyCrossHelicityCompiler ≡ false

canonicalMHDCyclicInvariantBidiFrontier : MHDCyclicInvariantBidiFrontier
canonicalMHDCyclicInvariantBidiFrontier =
  mhd-cyclic-invariant-bidi-frontier
    true refl true refl true refl
    true refl true refl true refl
    true refl true refl true refl true refl
    true refl true refl true refl
    true refl true refl true refl true refl
    true refl false refl false refl
