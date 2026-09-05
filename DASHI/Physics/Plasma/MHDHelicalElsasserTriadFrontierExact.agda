module DASHI.Physics.Plasma.MHDHelicalElsasserTriadFrontierExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- CURRENT BIDI FRONTIER FOR THE COMBINED HELICAL/ELSASSER TRIAD LANE.
------------------------------------------------------------------------

record MHDHelicalElsasserTriadFrontier : Set where
  constructor mhd-helical-elsasser-triad-frontier
  field
    combinedHypervoxelOwned : Bool
    combinedHypervoxelOwnedIsTrue : combinedHypervoxelOwned ≡ true

    helicityElsasserAxesSeparated : Bool
    helicityElsasserAxesSeparatedIsTrue : helicityElsasserAxesSeparated ≡ true

    counterpropagatingAdmissionOwned : Bool
    counterpropagatingAdmissionOwnedIsTrue : counterpropagatingAdmissionOwned ≡ true

    momentumAbstractZeroSumOwned : Bool
    momentumAbstractZeroSumOwnedIsTrue : momentumAbstractZeroSumOwned ≡ true

    momentumLiteralElsasserCommutatorClosed : Bool
    momentumLiteralElsasserCommutatorClosedIsFalse :
      momentumLiteralElsasserCommutatorClosed ≡ false

    inductionResidualClosed : Bool
    inductionResidualClosedIsFalse : inductionResidualClosed ≡ false

    fullMHDInvariantTransferClosed : Bool
    fullMHDInvariantTransferClosedIsFalse :
      fullMHDInvariantTransferClosed ≡ false

canonicalMHDHelicalElsasserTriadFrontier : MHDHelicalElsasserTriadFrontier
canonicalMHDHelicalElsasserTriadFrontier =
  mhd-helical-elsasser-triad-frontier
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
