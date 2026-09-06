{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.EUVSource.TinChargeStateSpectralStructureExact where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Coarse atomic/spectral ontology for laser-produced tin plasma.
--
-- Public ASML material establishes the gross fact that a hot tin plasma emits
-- useful EUV around 13.5 nm.  It does not, by itself, establish the exact
-- production charge-state distribution or the full line-by-line transition
-- assignment.  Those remain separate scientific obligations.

data TinChargeState : Set where
  SnNeutral : TinChargeState
  SnPlus1   : TinChargeState
  SnPlus2   : TinChargeState
  SnHigher  : Nat → TinChargeState

ChargePopulation : Set
ChargePopulation = TinChargeState → Nat

data SpectralBand : Set where
  InBand135 : SpectralBand
  OutOfBand : SpectralBand

record EmissionChannel : Set where
  constructor emissionChannel
  field
    upperCharge : TinChargeState
    lowerCharge : TinChargeState
    wavelengthTenthNm : Nat
    band : SpectralBand

open EmissionChannel public

-- Architecture-level 13.5 nm spectral coordinate.
-- The charge labels here are intentionally abstract placeholders rather than a
-- claim about the actual dominant production transition manifold.
publicBandCoordinate : EmissionChannel
publicBandCoordinate = emissionChannel (SnHigher 1) (SnHigher 1) 135 InBand135

publicBandWavelength : wavelengthTenthNm publicBandCoordinate ≡ 135
publicBandWavelength = refl

-- Scientific residuals that later atomic-physics modules must produce.
data SpectralResidual : Set where
  ExactChargeDistribution : SpectralResidual
  ExactDominantTransitionSet : SpectralResidual
  ExactLineStrengths : SpectralResidual
  ExactOpacityProfile : SpectralResidual
  ExactInBandFraction : SpectralResidual

-- Firewall:
--   tin plasma + 13.5 nm emission
-- does not identify a unique microscopic charge-state population or transition
-- set.  Those require atomic/plasma physics, not merely source architecture.
