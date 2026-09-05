{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Lithography.PhotonEnergyScalingExact where

open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.Semiconductor.Lithography.ASMLRayleighFixturesExact

-- Finite carrier for the inverse-wavelength part of
--
--   E_photon = h c / λ.
--
-- Holding h and c fixed, normalized photon-energy coordinates satisfy
--
--   E₁ λ₁ = E₂ λ₂.
--
-- This file intentionally separates the exact wavelength ratio from a later
-- physical-units bridge carrying Planck's constant, c and electron-volts.

record PhotonEnergyCoordinates : Set where
  constructor photonEnergyCoordinates
  field
    energyCoordinate     : Nat
    wavelengthCoordinate : Nat

open PhotonEnergyCoordinates public

SameHCPhotonEnergyRelation : PhotonEnergyCoordinates → PhotonEnergyCoordinates → Set
SameHCPhotonEnergyRelation x y =
  energyCoordinate x * wavelengthCoordinate x ≡
  energyCoordinate y * wavelengthCoordinate y

-- 193 nm / 13.5 nm = 1930 / 135 = 386 / 27.
-- Hence EUV photons have the exact normalized inverse-wavelength energy ratio
-- 386 : 27 relative to ArF photons, before inserting physical constants.

euvPhotonCoordinate : PhotonEnergyCoordinates
euvPhotonCoordinate = photonEnergyCoordinates 386 euvWavelengthTenthNm

arfPhotonCoordinate : PhotonEnergyCoordinates
arfPhotonCoordinate = photonEnergyCoordinates 27 arfWavelengthTenthNm

euvArfPhotonEnergyScaling :
  SameHCPhotonEnergyRelation euvPhotonCoordinate arfPhotonCoordinate
euvArfPhotonEnergyScaling = refl

-- Regression exposing the exact common product.
euvPhotonProductExact : 386 * euvWavelengthTenthNm ≡ 52110
euvPhotonProductExact = refl

arfPhotonProductExact : 27 * arfWavelengthTenthNm ≡ 52110
arfPhotonProductExact = refl
