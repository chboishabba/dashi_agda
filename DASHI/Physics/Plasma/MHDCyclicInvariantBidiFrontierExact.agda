module DASHI.Physics.Plasma.MHDCyclicInvariantBidiFrontierExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- CYCLIC INVARIANT FRONTIER AFTER PRE-NORM CROSS-POLLINATION
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

    threeOutputCyclicCarrierOwned : Bool
    threeOutputCyclicCarrierOwnedIsTrue :
      threeOutputCyclicCarrierOwned ≡ true

    couplingExchangeAntisymmetryShapeOwned : Bool
    couplingExchangeAntisymmetryShapeOwnedIsTrue :
      couplingExchangeAntisymmetryShapeOwned ≡ true

    fullModalTransferSkewWeldOwned : Bool
    fullModalTransferSkewWeldOwnedIsFalse :
      fullModalTransferSkewWeldOwned ≡ false

    threeOutputSkewDecompositionSocketOwned : Bool
    threeOutputSkewDecompositionSocketOwnedIsTrue :
      threeOutputSkewDecompositionSocketOwned ≡ true

    literalMHDPlusSkewExchangeDecompositionOwned : Bool
    literalMHDPlusSkewExchangeDecompositionOwnedIsFalse :
      literalMHDPlusSkewExchangeDecompositionOwned ≡ false

    literalMHDMinusSkewExchangeDecompositionOwned : Bool
    literalMHDMinusSkewExchangeDecompositionOwnedIsFalse :
      literalMHDMinusSkewExchangeDecompositionOwned ≡ false

    literalPressureProjectionCancellationOwned : Bool
    literalPressureProjectionCancellationOwnedIsFalse :
      literalPressureProjectionCancellationOwned ≡ false

    pseudoEnergyToInvariantCompilerOwned : Bool
    pseudoEnergyToInvariantCompilerOwnedIsTrue :
      pseudoEnergyToInvariantCompilerOwned ≡ true

    totalEnergyLiteralTriadConservationOwned : Bool
    totalEnergyLiteralTriadConservationOwnedIsFalse :
      totalEnergyLiteralTriadConservationOwned ≡ false

    crossHelicityLiteralTriadConservationOwned : Bool
    crossHelicityLiteralTriadConservationOwnedIsFalse :
      crossHelicityLiteralTriadConservationOwned ≡ false

canonicalMHDCyclicInvariantBidiFrontier : MHDCyclicInvariantBidiFrontier
canonicalMHDCyclicInvariantBidiFrontier =
  mhd-cyclic-invariant-bidi-frontier
    true refl true refl true refl true refl
    false refl true refl
    false refl false refl false refl
    true refl false refl false refl
