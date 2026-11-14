{-# OPTIONS --safe #-}
module DASHI.Physics.Gravity.KSW668FiveDimensionalEinsteinScalarFRWFriedmannExact where

------------------------------------------------------------------------
-- D1/D2 original real-physics algebraic 5D FRW Einstein–scalar crosswalk.
-- Model in scripts/ksw668_kk_einstein_scalar_cosmology.py:
--   ds5² = -dt² + t^(1/2) (dx²+dy²+dz²+dw²)
--   phi(t) = sqrt(3)/2 log(t), t>0, w mod 4.
-- Einstein equation G_AB = T_AB, kappa5=1, Lambda=0.
--
-- This Agda proof owns the exact RATIONAL Friedmann algebra expressed in
-- u = 1/t: H=u/4, Hdot=-u²/4, rho=p=3u²/8, phidot²=3u²/4.
-- Full metric differentiation, real sqrt/log analytic carrier, Christoffel,
-- Riemann and Einstein tensors are verified by the independent SymPy script,
-- NOT by this rational Agda module. The original analytic weld remains OPEN.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

fourth : ℚ
fourth = (+ 1) / 4

threeEighths : ℚ
threeEighths = (+ 3) / 8

threeFourths : ℚ
threeFourths = (+ 3) / 4

Hubble5 : ℚ → ℚ
Hubble5 u = fourth * u

HubbleDerivative5 : ℚ → ℚ
HubbleDerivative5 u = - (fourth * (u * u))

scalarEnergyDensity5 : ℚ → ℚ
scalarEnergyDensity5 u = threeEighths * (u * u)

scalarPressure5 : ℚ → ℚ
scalarPressure5 = scalarEnergyDensity5

scalarRateSquared5 : ℚ → ℚ
scalarRateSquared5 u = threeFourths * (u * u)

einstein00FiveSpatialMetric :
  ∀ u →
  ((+ 6) * (Hubble5 u * Hubble5 u))
    ≡ scalarEnergyDensity5 u
einstein00FiveSpatialMetric u = solve (u ∷ [])

einsteinSpatialFourDirections :
  ∀ u →
  - ((+ 3) * HubbleDerivative5 u)
  - ((+ 6) * (Hubble5 u * Hubble5 u))
    ≡ scalarPressure5 u
einsteinSpatialFourDirections u = solve (u ∷ [])

canonicalScalarKineticEnergy5 :
  ∀ u →
  ((+ 1) / 2) * scalarRateSquared5 u
    ≡ scalarEnergyDensity5 u
canonicalScalarKineticEnergy5 u = solve (u ∷ [])

stiffMatterEquationOfState5 :
  ∀ u →
  scalarPressure5 u ≡ scalarEnergyDensity5 u
stiffMatterEquationOfState5 u = refl

ricciScalarFiveD :
  ℚ → ℚ
ricciScalarFiveD u = - (threeFourths * (u * u))

scalarEinsteinTraceFiveD :
  ∀ u →
  - (((+ 3) / 2) * ricciScalarFiveD u)
    ≡ (+ 3) * scalarEnergyDensity5 u
scalarEinsteinTraceFiveD u = solve (u ∷ [])

------------------------------------------------------------------------
-- Exact-kernel closures are the Friedmann/trace algebra ON THE ORIGINAL
-- RATIONAL COEFFICIENTS. Positivity for cosmic t>0, analytic original
-- phi=√3/2 log t, and geodesic/Einstein PDE are not smuggled into Set.
------------------------------------------------------------------------

rationalFRWSourceOnly : Bool
rationalFRWSourceOnly = true

interacting5DEinsteinMetricKernelAcceptedHere : Bool
interacting5DEinsteinMetricKernelAcceptedHere = false

physicalObserverDetection : Bool
physicalObserverDetection = false

rationalFRWSourceOnlyIsTrue : rationalFRWSourceOnly ≡ true
rationalFRWSourceOnlyIsTrue = refl
