{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Lithography.EqualEnergyPhotonCountScalingExact where

open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.Semiconductor.Lithography.ASMLRayleighFixturesExact

-- For fixed total radiant energy D and E_photon = hc/λ,
--
--   N = D / E_photon = D λ / hc.
--
-- Thus equal-energy exposures have photon counts proportional to wavelength.
-- This finite seam owns only that scaling law; it does not assert an actual
-- scanner dose, resist absorption fraction or stochastic defect rate.

record EqualEnergyPhotonCountCoordinates : Set where
  constructor equalEnergyPhotonCountCoordinates
  field
    photonCountCoordinate : Nat
    wavelengthCoordinate  : Nat

open EqualEnergyPhotonCountCoordinates public

EqualEnergyCountRelation :
  EqualEnergyPhotonCountCoordinates →
  EqualEnergyPhotonCountCoordinates → Set
EqualEnergyCountRelation x y =
  photonCountCoordinate x * wavelengthCoordinate y ≡
  photonCountCoordinate y * wavelengthCoordinate x

-- Since 13.5/193 = 27/386, at equal radiant energy the normalized EUV:ArF
-- photon-count ratio is 27:386.

euvEqualEnergyCount : EqualEnergyPhotonCountCoordinates
euvEqualEnergyCount =
  equalEnergyPhotonCountCoordinates 27 euvWavelengthTenthNm

arfEqualEnergyCount : EqualEnergyPhotonCountCoordinates
arfEqualEnergyCount =
  equalEnergyPhotonCountCoordinates 386 arfWavelengthTenthNm

euvArfEqualEnergyPhotonCountScaling :
  EqualEnergyCountRelation euvEqualEnergyCount arfEqualEnergyCount
euvArfEqualEnergyPhotonCountScaling = refl

leftProductExact :
  27 * arfWavelengthTenthNm ≡ 52110
leftProductExact = refl

rightProductExact :
  386 * euvWavelengthTenthNm ≡ 52110
rightProductExact = refl

-- Scientific firewall:
-- fewer incident photons at equal radiant energy is not itself a theorem of
-- larger printed stochastic error.  That bridge requires an absorption/event
-- model and a stochastic resist/secondary-electron producer.
