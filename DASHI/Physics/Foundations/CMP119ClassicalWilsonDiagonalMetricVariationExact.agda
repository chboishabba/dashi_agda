{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119ClassicalWilsonDiagonalMetricVariationExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)\nopen import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_; -_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

------------------------------------------------------------------------
-- CLASSICAL d=4 YANG--MILLS / WILSON DIAGONAL METRIC VARIATION
--
-- At the Euclidean identity metric,
--
--   d[ sqrt(g) g^{mu mu} g^{nu nu} ][h_aa]
--      = 1/2 - delta(a,mu) - delta(a,nu).
--
-- For the six independent plaquette-orientation energies
--
--   E01 E02 E03 E12 E13 E23
--
-- this gives four exact diagonal metric variations.  Their sum vanishes
-- pointwise: classical four-dimensional YM is conformally traceless.
------------------------------------------------------------------------

half : ℚ
half = + 1 / 2

record SixPlaquetteOrientationEnergies : Set where
  field
    e01 e02 e03 e12 e13 e23 : ℚ

open SixPlaquetteOrientationEnergies public

dS00 : SixPlaquetteOrientationEnergies → ℚ
dS00 e =
  (- half) * e01 e
  + (- half) * e02 e
  + (- half) * e03 e
  + half * e12 e
  + half * e13 e
  + half * e23 e

dS11 : SixPlaquetteOrientationEnergies → ℚ
dS11 e =
  (- half) * e01 e
  + half * e02 e
  + half * e03 e
  + (- half) * e12 e
  + (- half) * e13 e
  + half * e23 e

dS22 : SixPlaquetteOrientationEnergies → ℚ
dS22 e =
  half * e01 e
  + (- half) * e02 e
  + half * e03 e
  + (- half) * e12 e
  + half * e13 e
  + (- half) * e23 e

dS33 : SixPlaquetteOrientationEnergies → ℚ
dS33 e =
  half * e01 e
  + half * e02 e
  + (- half) * e03 e
  + half * e12 e
  + (- half) * e13 e
  + (- half) * e23 e

classicalDiagonalMetricTrace :
  SixPlaquetteOrientationEnergies → ℚ
classicalDiagonalMetricTrace e =
  dS00 e + dS11 e + dS22 e + dS33 e

classicalDiagonalMetricTraceIsZero :
  ∀ e → classicalDiagonalMetricTrace e ≡ 0ℚ
classicalDiagonalMetricTraceIsZero e =
  ℚRing.solve-∀
    (e01 e) (e02 e) (e03 e)
    (e12 e) (e13 e) (e23 e)

record FiniteSixPlaquetteEnergyFamily (Configuration : Set) : Set₁ where
  field
    orientationEnergies :
      Configuration → SixPlaquetteOrientationEnergies

open FiniteSixPlaquetteEnergyFamily public

classicalActionVariation00 :
  ∀ {Configuration} →
  FiniteSixPlaquetteEnergyFamily Configuration →
  Configuration → ℚ
classicalActionVariation00 family configuration =
  dS00 (orientationEnergies family configuration)

classicalActionVariation11 :
  ∀ {Configuration} →
  FiniteSixPlaquetteEnergyFamily Configuration →
  Configuration → ℚ
classicalActionVariation11 family configuration =
  dS11 (orientationEnergies family configuration)

classicalActionVariation22 :
  ∀ {Configuration} →
  FiniteSixPlaquetteEnergyFamily Configuration →
  Configuration → ℚ
classicalActionVariation22 family configuration =
  dS22 (orientationEnergies family configuration)

classicalActionVariation33 :
  ∀ {Configuration} →
  FiniteSixPlaquetteEnergyFamily Configuration →
  Configuration → ℚ
classicalActionVariation33 family configuration =
  dS33 (orientationEnergies family configuration)

classicalActionVariationTraceZero :
  ∀ {Configuration}
    (family : FiniteSixPlaquetteEnergyFamily Configuration)
    configuration →
  classicalActionVariation00 family configuration
  + classicalActionVariation11 family configuration
  + classicalActionVariation22 family configuration
  + classicalActionVariation33 family configuration
  ≡ 0ℚ
classicalActionVariationTraceZero family configuration =
  classicalDiagonalMetricTraceIsZero
    (orientationEnergies family configuration)
