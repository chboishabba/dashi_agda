module DASHI.Physics.Plasma.MHDHelicalTriadBidiFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.MHDHelicalCoefficientAnatomyExact as Anatomy
import DASHI.Physics.Plasma.MHDMomentumTriadZeroSumBidiExact as Momentum
import DASHI.Physics.Plasma.HelicityElsasserBinaryAxesExact as Axes

------------------------------------------------------------------------
-- CURRENT MHD HELICAL-TRIAD BIDI FRONTIER
------------------------------------------------------------------------

record MHDHelicalTriadStatus : Set where
  constructor mhd-helical-triad-status
  field
    helicalMHDCoefficientAnatomyOwned : Bool
    helicalMHDCoefficientAnatomyOwnedIsTrue :
      helicalMHDCoefficientAnatomyOwned ≡ true

    helicityElsasserAxesSeparated : Bool
    helicityElsasserAxesSeparatedIsTrue :
      helicityElsasserAxesSeparated ≡ true

    abstractMomentumCyclicZeroSumOwned : Bool
    abstractMomentumCyclicZeroSumOwnedIsTrue :
      abstractMomentumCyclicZeroSumOwned ≡ true

    literalMomentumSameObjectWeldClosed : Bool
    literalMomentumSameObjectWeldClosedIsFalse :
      literalMomentumSameObjectWeldClosed ≡ false

    inductionSectorZeroSumOwned : Bool
    inductionSectorZeroSumOwnedIsFalse :
      inductionSectorZeroSumOwned ≡ false

    fullElsasserHelicalTriadODEOwned : Bool
    fullElsasserHelicalTriadODEOwnedIsFalse :
      fullElsasserHelicalTriadODEOwned ≡ false

    invariantTransferClassificationOwned : Bool
    invariantTransferClassificationOwnedIsFalse :
      invariantTransferClassificationOwned ≡ false

canonicalMHDHelicalTriadStatus : MHDHelicalTriadStatus
canonicalMHDHelicalTriadStatus =
  mhd-helical-triad-status
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Reverse/BIDI acquisition obligations.
------------------------------------------------------------------------

record NextMHDHelicalTriadObligations : Set where
  constructor next-mhd-helical-triad-obligations
  field
    recoverLiteralGeometricTripleProduct : Bool
    recoverLiteralGeometricTripleProductIsTrue :
      recoverLiteralGeometricTripleProduct ≡ true

    proveCyclicOrientationConvention : Bool
    proveCyclicOrientationConventionIsTrue :
      proveCyclicOrientationConvention ≡ true

    instantiateVelocityAndMagneticAmplitudeChannels : Bool
    instantiateVelocityAndMagneticAmplitudeChannelsIsTrue :
      instantiateVelocityAndMagneticAmplitudeChannels ≡ true

    deriveElsasserSectorODEFromUBSystem : Bool
    deriveElsasserSectorODEFromUBSystemIsTrue :
      deriveElsasserSectorODEFromUBSystem ≡ true

    testInductionCoefficientForOwnCancellation : Bool
    testInductionCoefficientForOwnCancellationIsTrue :
      testInductionCoefficientForOwnCancellation ≡ true

canonicalNextMHDHelicalTriadObligations : NextMHDHelicalTriadObligations
canonicalNextMHDHelicalTriadObligations =
  next-mhd-helical-triad-obligations
    true refl true refl true refl true refl true refl

record MHDHelicalBidiAuthorityBoundary : Set where
  constructor mhd-helical-bidi-authority-boundary
  field
    momentumCancellationPromotesWholeMHDNonlinearity : Bool
    momentumCancellationPromotesWholeMHDNonlinearityIsFalse :
      momentumCancellationPromotesWholeMHDNonlinearity ≡ false

    helicalSignClassificationPromotesElsasserClassification : Bool
    helicalSignClassificationPromotesElsasserClassificationIsFalse :
      helicalSignClassificationPromotesElsasserClassification ≡ false

    transferDirectionFollowsCoefficientZeroSumAlone : Bool
    transferDirectionFollowsCoefficientZeroSumAloneIsFalse :
      transferDirectionFollowsCoefficientZeroSumAlone ≡ false

canonicalMHDHelicalBidiAuthorityBoundary : MHDHelicalBidiAuthorityBoundary
canonicalMHDHelicalBidiAuthorityBoundary =
  mhd-helical-bidi-authority-boundary false refl false refl false refl
