module DASHI.Physics.GR.SchutzholdSpecializedMaxwellVariationExact where

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; ½; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

------------------------------------------------------------------------
-- SPECIALIZED MAXWELL METRIC VARIATION FOR THE SCHUTZHOLD SECTOR
--
-- Sector:
--   ds^2 = dt^2 - (1+h) dx^2 - (1-h) dy^2 - dz^2
--   A = A_z(t,x,y) e_z
--
-- We work directly with the squared derivative densities
--   T = (dt A_z)^2, X = (dx A_z)^2, Y = (dy A_z)^2.
-- This is enough to prove the exact first-order algebra behind source Eq. (3)
-- without waiting for a fully generic tensor-index implementation.
------------------------------------------------------------------------

lagrangianDensity : ℚ → ℚ → ℚ → ℚ → ℚ
lagrangianDensity h T X Y =
  ½ * (T - ((1ℚ - h) * X + (1ℚ + h) * Y))

flatLagrangianDensity : ℚ → ℚ → ℚ → ℚ
flatLagrangianDensity T X Y = ½ * (T - (X + Y))

metricVariationDensity : ℚ → ℚ → ℚ → ℚ
metricVariationDensity δh X Y = ½ * δh * (X - Y)

lagrangianSplitsFlatPlusMetricVariation :
  ∀ h T X Y →
  lagrangianDensity h T X Y
  ≡ flatLagrangianDensity T X Y + metricVariationDensity h X Y
lagrangianSplitsFlatPlusMetricVariation = solve-∀

exactFiniteMetricFirstVariation :
  ∀ h δh T X Y →
  lagrangianDensity (h + δh) T X Y - lagrangianDensity h T X Y
  ≡ metricVariationDensity δh X Y
exactFiniteMetricFirstVariation = solve-∀

------------------------------------------------------------------------
-- Stress-pairing normal form.
--
-- On this one-dimensional metric-perturbation fibre, the Hilbert pairing is
-- represented by the anisotropic transverse stress coordinate (X-Y).
------------------------------------------------------------------------

selectedStressCoordinate : ℚ → ℚ → ℚ
selectedStressCoordinate X Y = X - Y

selectedMetricStressPairing : ℚ → ℚ → ℚ → ℚ
selectedMetricStressPairing δh X Y =
  ½ * δh * selectedStressCoordinate X Y

specializedHilbertPairing :
  ∀ h δh T X Y →
  lagrangianDensity (h + δh) T X Y - lagrangianDensity h T X Y
  ≡ selectedMetricStressPairing δh X Y
specializedHilbertPairing = solve-∀

swapTransverseStressSign :
  ∀ X Y → selectedStressCoordinate Y X ≡ 0ℚ - selectedStressCoordinate X Y
swapTransverseStressSign = solve-∀

swapTransverseMetricVariationSign :
  ∀ δh X Y →
  selectedMetricStressPairing δh Y X
  ≡ 0ℚ - selectedMetricStressPairing δh X Y
swapTransverseMetricVariationSign = solve-∀

------------------------------------------------------------------------
-- Eq. (7) first-order dispersion algebra.
------------------------------------------------------------------------

dispersionSquare : ℚ → ℚ → ℚ → ℚ
dispersionSquare h Kx2 Ky2 =
  (1ℚ - h) * Kx2 + (1ℚ + h) * Ky2

flatDispersionSquare : ℚ → ℚ → ℚ
flatDispersionSquare Kx2 Ky2 = Kx2 + Ky2

dispersionMetricCorrection : ℚ → ℚ → ℚ → ℚ
dispersionMetricCorrection h Kx2 Ky2 = h * (Ky2 - Kx2)

dispersionSplitsFlatPlusCorrection :
  ∀ h Kx2 Ky2 →
  dispersionSquare h Kx2 Ky2
  ≡ flatDispersionSquare Kx2 Ky2 + dispersionMetricCorrection h Kx2 Ky2
dispersionSplitsFlatPlusCorrection = solve-∀

exactDispersionFiniteVariation :
  ∀ h δh Kx2 Ky2 →
  dispersionSquare (h + δh) Kx2 Ky2 - dispersionSquare h Kx2 Ky2
  ≡ δh * (Ky2 - Kx2)
exactDispersionFiniteVariation = solve-∀

record SpecializedVariationScope : Set where
  constructor specialized-variation-scope
  field
    sourceEq3AlgebraDerived : Bool
    exactFiniteMetricVariationDerived : Bool
    selectedStressPairingDerived : Bool
    transverseSwapReversalDerived : Bool
    sourceEq7LinearMetricCorrectionDerived : Bool
    requiresGenericCurvedSpacetimeTensorCalculusForThisSector : Bool
    replacesGeneralHilbertStressTheoremEverywhere : Bool

canonicalSpecializedVariationScope : SpecializedVariationScope
canonicalSpecializedVariationScope =
  specialized-variation-scope true true true true true false false
