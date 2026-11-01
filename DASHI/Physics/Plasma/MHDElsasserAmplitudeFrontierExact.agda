module DASHI.Physics.Plasma.MHDElsasserAmplitudeFrontierExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- CURRENT FRONTIER AFTER EXACT ELSASSER AMPLITUDE RECHART
------------------------------------------------------------------------

record MHDElsasserAmplitudeFrontier : Set where
  constructor mhd-elsasser-amplitude-frontier
  field
    exactDivisionFreeMomentumRechartOwned : Bool
    exactDivisionFreeMomentumRechartOwnedIsTrue :
      exactDivisionFreeMomentumRechartOwned ≡ true

    exactDivisionFreeInductionRechartOwned : Bool
    exactDivisionFreeInductionRechartOwnedIsTrue :
      exactDivisionFreeInductionRechartOwned ≡ true

    sameSignElsasserProductsEliminatedOwned : Bool
    sameSignElsasserProductsEliminatedOwnedIsTrue :
      sameSignElsasserProductsEliminatedOwned ≡ true

    mixedSectorSupportClassificationOwned : Bool
    mixedSectorSupportClassificationOwnedIsTrue :
      mixedSectorSupportClassificationOwned ≡ true

    momentumSymmetricMixedCombinationOwned : Bool
    momentumSymmetricMixedCombinationOwnedIsTrue :
      momentumSymmetricMixedCombinationOwned ≡ true

    inductionAntisymmetricMixedCombinationOwned : Bool
    inductionAntisymmetricMixedCombinationOwnedIsTrue :
      inductionAntisymmetricMixedCombinationOwned ≡ true

    literalCoefficientTimesAmplitudeTriadODEClosed : Bool
    literalCoefficientTimesAmplitudeTriadODEClosedIsFalse :
      literalCoefficientTimesAmplitudeTriadODEClosed ≡ false

    nonlinearInvariantTransferClosed : Bool
    nonlinearInvariantTransferClosedIsFalse :
      nonlinearInvariantTransferClosed ≡ false

canonicalMHDElsasserAmplitudeFrontier : MHDElsasserAmplitudeFrontier
canonicalMHDElsasserAmplitudeFrontier =
  mhd-elsasser-amplitude-frontier
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
