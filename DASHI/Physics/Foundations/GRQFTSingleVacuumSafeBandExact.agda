{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTSingleVacuumSafeBandExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 1ℚ; _/_; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Foundations.GRQFTSingleVacuumIsraelKottlerExact as Single

------------------------------------------------------------------------
-- ONE-COORDINATE SAFE BAND FOR THE SINGLE-VACUUM BRANCH
--
-- Fix y = 9x/10.  Substitution into the exact rational-square Israel margins
-- leaves one interior lapse coordinate x.  The factorisations below show why
-- the rational open band
--
--     3/5 < x < 7/10
--
-- is a convenient sufficient design region: mass, outward acceleration,
-- NEC/DEC and SEC-violation margins all have the desired orientation there.
-- Order propagation is deliberately kept separate from these exact polynomial
-- identities, so no hidden positivity/cancellation assumptions are introduced.
------------------------------------------------------------------------

nineTenths : ℚ
nineTenths = Int.+ 9 / 10

safeLowerX : ℚ
safeLowerX = Int.+ 3 / 5

safeUpperX : ℚ
safeUpperX = Int.+ 7 / 10

sourceQSafeLower : ℚ
sourceQSafeLower = Int.+ 9 / 17

sourceQSafeUpper : ℚ
sourceQSafeUpper = Int.+ 3 / 4

exteriorLapseFromInterior : ℚ → ℚ
exteriorLapseFromInterior x = nineTenths * x

massFactorization :
  ∀ radius x →
  Single.sameVacuumMass radius x (exteriorLapseFromInterior x)
  ≡ (Int.+ 19 / 200) * radius * x * x
massFactorization radius x = solve (radius ∷ x ∷ [])

outwardFactorization :
  ∀ radius x →
  Single.sameVacuumOutwardScaled radius x (exteriorLapseFromInterior x)
  ≡ radius * (1ℚ - (Int.+ 219 / 200) * x * x)
outwardFactorization radius x = solve (radius ∷ x ∷ [])

necDecFactorization :
  ∀ radius x →
  Single.sameVacuumNECDECMargin radius x (exteriorLapseFromInterior x)
  ≡ (radius * x / (Int.+ 200 / 1))
      * ((Int.+ 57 / 1) * x * x - (Int.+ 20 / 1))
necDecFactorization radius x = solve (radius ∷ x ∷ [])

secViolationFactorization :
  ∀ radius x →
  Single.sameVacuumSECViolationMargin radius x (exteriorLapseFromInterior x)
  ≡ (radius * x / (Int.+ 200 / 1))
      * ((Int.+ 20 / 1) - (Int.+ 39 / 1) * x * x)
secViolationFactorization radius x = solve (radius ∷ x ∷ [])

pressureTensionFactorization :
  ∀ radius x →
  Single.sameVacuumPressureTensionMargin radius x (exteriorLapseFromInterior x)
  ≡ (radius * x / (Int.+ 200 / 1))
      * ((Int.+ 20 / 1) - (Int.+ 21 / 1) * x * x)
pressureTensionFactorization radius x = solve (radius ∷ x ∷ [])

------------------------------------------------------------------------
-- SOURCE-CONIC HOMOGENEOUS PARAMETERIZATION
--
-- For q = lambda t^2, write
--
--   X = 3-q,  D = 3+q,  R_num = 6t.
--
-- Then X/D and R_num/D are the usual rational parametrization of
-- x^2 + (lambda/3) R^2 = 1.  We prove the denominator-cleared identity, which
-- is the exact form required by the current no-hidden-cancellation discipline.
------------------------------------------------------------------------

conicQ : ℚ → ℚ → ℚ
conicQ lambda t = lambda * t * t

conicXNumerator : ℚ → ℚ → ℚ
conicXNumerator lambda t = (Int.+ 3 / 1) - conicQ lambda t

conicDenominator : ℚ → ℚ → ℚ
conicDenominator lambda t = (Int.+ 3 / 1) + conicQ lambda t

conicRadiusNumerator : ℚ → ℚ
conicRadiusNumerator t = (Int.+ 6 / 1) * t

conicHomogeneousIdentity :
  ∀ lambda t →
  (Int.+ 3 / 1)
    * conicXNumerator lambda t * conicXNumerator lambda t
  + lambda * conicRadiusNumerator t * conicRadiusNumerator t
  ≡
  (Int.+ 3 / 1)
    * conicDenominator lambda t * conicDenominator lambda t
conicHomogeneousIdentity lambda t = solve (lambda ∷ t ∷ [])

-- The safe x-band corresponds to the following q endpoints under
-- x=(3-q)/(3+q), expressed without division.
sourceQLowerMapsToUpperX :
  (Int.+ 10 / 1) * ((Int.+ 3 / 1) - sourceQSafeLower)
  ≡ (Int.+ 7 / 1) * ((Int.+ 3 / 1) + sourceQSafeLower)
sourceQLowerMapsToUpperX = solve []

sourceQUpperMapsToLowerX :
  (Int.+ 5 / 1) * ((Int.+ 3 / 1) - sourceQSafeUpper)
  ≡ (Int.+ 3 / 1) * ((Int.+ 3 / 1) + sourceQSafeUpper)
sourceQUpperMapsToLowerX = solve []

record SingleVacuumSafeBandBoundary : Set where
  constructor single-vacuum-safe-band-boundary
  field
    oneLapseCoordinateAfterFixedRatio : Bool
    massPolynomialFactorized : Bool
    outwardMarginPolynomialFactorized : Bool
    necDecMarginPolynomialFactorized : Bool
    secViolationMarginPolynomialFactorized : Bool
    sourceConicHomogeneousParameterizationConstructed : Bool
    safeXBandHasRationalEndpoints : Bool
    safeSourceQBandHasRationalEndpoints : Bool

canonicalSingleVacuumSafeBandBoundary : SingleVacuumSafeBandBoundary
canonicalSingleVacuumSafeBandBoundary =
  single-vacuum-safe-band-boundary
    true true true true true true true true
