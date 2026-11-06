{-# OPTIONS --safe #-}
module DASHI.Geometry.GielisSpectralSIScaleExact where

------------------------------------------------------------------------
-- SAME SI/MLT OWNER FOR CONTINUUM / FINITE LAPLACIAN LENGTH SCALING
--
-- For a length-scaled domain L Ω_m, the Dirichlet Laplacian carries
-- L^-2 and each eigenvalue scales as 1/L^2. The exact eigenfunction
-- pullback is a standard continuum theorem (not manufactured here).
-- This source proves the actual machine-readable MLT/SI dimensional
-- relations AND transports numeric inverse-area scaling on the
-- repository's established Mechanical.Quantity / SIIndexedQuantity.
--
-- The finite raster eigenvalues computed at unit spacing and the
-- continuum eigenvalues are DIFFERENT spectral objects. Do not
-- equate them without the actual G12 finite-to-continuum proof.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Data.Integer using (+_; -[1+_])
open import Data.Rational.Base using (ℚ; _*_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Units.SI as SI
import DASHI.Physics.Units.MechanicalDimensionExact as Mechanical
import DASHI.Physics.YangMills.YangMillsSIScalingEndpointExact as ExistingSI

spectralEigenvalueDimension : Mechanical.MechanicalDimension
spectralEigenvalueDimension = Mechanical.inverseAreaDimension

spectralInverseSquareMetre : SI.Dimension
spectralInverseSquareMetre =
  SI.dim SI.minusTwo SI.zeroI SI.zeroI
    SI.zeroI SI.zeroI SI.zeroI SI.zeroI

nativeSpectralDimensionMatchesSI :
  ExistingSI.mechanicalToSI spectralEigenvalueDimension
  ≡ spectralInverseSquareMetre
nativeSpectralDimensionMatchesSI = refl

inverseAreaTimesAreaDimensionless :
  Mechanical._⊗ᴰ_
    spectralEigenvalueDimension Mechanical.areaDimension
  ≡ Mechanical.dimensionless
inverseAreaTimesAreaDimensionless = refl

-- Unitless eigenvalue times a physically calibrated inverse-area
-- coordinate scale: the result has inverse-square-metre units.
dimensionlessEigenvalue :
  ℚ → Mechanical.Quantity ℚ Mechanical.dimensionless
dimensionlessEigenvalue = Mechanical.quantity

inverseAreaScale :
  ℚ → Mechanical.Quantity ℚ spectralEigenvalueDimension
inverseAreaScale = Mechanical.quantity

scaleEigenvalueRaw :
  Mechanical.Quantity ℚ Mechanical.dimensionless →
  Mechanical.Quantity ℚ spectralEigenvalueDimension →
  Mechanical.Quantity ℚ
    (Mechanical._⊗ᴰ_ Mechanical.dimensionless
      spectralEigenvalueDimension)
scaleEigenvalueRaw value invArea =
  Mechanical.multiplyQuantity _*_ value invArea

scaleEigenvalue :
  Mechanical.Quantity ℚ Mechanical.dimensionless →
  Mechanical.Quantity ℚ spectralEigenvalueDimension →
  Mechanical.Quantity ℚ spectralEigenvalueDimension
scaleEigenvalue value invArea = scaleEigenvalueRaw value invArea

scaleEigenvalueExactMagnitude :
  ∀ value invArea →
  Mechanical.magnitude
    (scaleEigenvalue
      (dimensionlessEigenvalue value)
      (inverseAreaScale invArea))
  ≡ value * invArea
scaleEigenvalueExactMagnitude value invArea = refl

scaleEigenvalueInActualSI :
  Mechanical.Quantity ℚ Mechanical.dimensionless →
  Mechanical.Quantity ℚ spectralEigenvalueDimension →
  ExistingSI.SIIndexedQuantity ℚ spectralInverseSquareMetre
scaleEigenvalueInActualSI value invArea =
  subst (ExistingSI.SIIndexedQuantity ℚ)
    nativeSpectralDimensionMatchesSI
    (ExistingSI.mechanicalQuantityToSI
      (scaleEigenvalue value invArea))

scaleEigenvalueSIScalar :
  ∀ value invArea →
  ExistingSI.magnitude
    (scaleEigenvalueInActualSI
      (dimensionlessEigenvalue value)
      (inverseAreaScale invArea))
  ≡ value * invArea
scaleEigenvalueSIScalar value invArea = refl

-- Notice: an actual wavelength/frequency requires a wave-speed
-- constitutive law in addition to an inverse-area Laplace eigenvalue.
-- These finite typed equations do NOT assert a physical frequency.
