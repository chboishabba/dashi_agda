{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Lithography.ASMLRayleighFixturesExact where

open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.Semiconductor.Lithography.RayleighCriterionExact

-- Public nominal ASML technology coordinates represented as exact scaled Nats.
-- Wavelengths are in tenths of a nanometre; numerical apertures are in
-- hundredths.  These are source-coordinate fixtures, not proofs of complete
-- scanner performance.

euvWavelengthTenthNm : Nat
euvWavelengthTenthNm = 135

arfWavelengthTenthNm : Nat
arfWavelengthTenthNm = 1930

standardEuvNAHundredths : Nat
standardEuvNAHundredths = 33

highEuvNAHundredths : Nat
highEuvNAHundredths = 55

arfImmersionNAHundredths : Nat
arfImmersionNAHundredths = 135

-- Holding wavelength and k₁ fixed in the ideal Rayleigh relation, the
-- 0.33 -> 0.55 NA change has the exact normalized inverse-aperture witness
--
--   5 · 33 = 3 · 55.
--
-- Hence the idealized CD coordinate changes by the ratio 3/5.  This theorem
-- does not claim that physical on-wafer CD, yield, depth of focus, stochastic
-- defects, or throughput scale by this ratio.
highNaInverseApertureScaling :
  5 * standardEuvNAHundredths ≡ 3 * highEuvNAHundredths
highNaInverseApertureScaling = refl

-- Exact finite arithmetic underlying a λ/NA comparison between nominal EUV
-- (13.5 nm, NA 0.33) and ArF immersion (193 nm, NA 1.35).
euvArfiLeftCrossProduct :
  euvWavelengthTenthNm * arfImmersionNAHundredths ≡ 18225
euvArfiLeftCrossProduct = refl

arfArfiRightCrossProduct :
  arfWavelengthTenthNm * standardEuvNAHundredths ≡ 63690
arfArfiRightCrossProduct = refl

euvVsArfiRayleighProxyGap :
  RayleighProxyCrossGap
    euvWavelengthTenthNm
    standardEuvNAHundredths
    arfWavelengthTenthNm
    arfImmersionNAHundredths
euvVsArfiRayleighProxyGap = strictGap 45464 refl

-- A normalized pair of exact Rayleigh-law fixtures making the same 0.33/0.55
-- inverse-aperture relation executable.  The common wavelength coordinate 165
-- is a normalization chosen solely so both finite equations reduce by refl;
-- it is not an ASML wavelength claim.
standardNormalizedRayleigh : RayleighCoordinates
standardNormalizedRayleigh =
  rayleighCoordinates 5 1 165 standardEuvNAHundredths

standardNormalizedRayleighLaw : RayleighLaw standardNormalizedRayleigh
standardNormalizedRayleighLaw = refl

highNaNormalizedRayleigh : RayleighCoordinates
highNaNormalizedRayleigh =
  rayleighCoordinates 3 1 165 highEuvNAHundredths

highNaNormalizedRayleighLaw : RayleighLaw highNaNormalizedRayleigh
highNaNormalizedRayleighLaw = refl
