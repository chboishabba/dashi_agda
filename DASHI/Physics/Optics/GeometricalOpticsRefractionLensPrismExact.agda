module DASHI.Physics.Optics.GeometricalOpticsRefractionLensPrismExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- PROVENANCE / SCOPE
--
-- Standard geometrical optics:
--   Snell: n1 sin(theta1) = n2 sin(theta2)
--   critical-angle / total-internal-reflection condition
--   wavelength-dependent refractive index n(lambda) for dispersion
--   thin-lens equation 1/f = 1/do + 1/di
--   lens-maker equation in air
--     1/f = (n - 1) (1/R1 - 1/R2)
--
-- This module is algebra-parameterised.  It certifies supplied geometrical-
-- optics solutions; it is not a Maxwell-wave, diffraction, aberration, or
-- thick-lens solver.
------------------------------------------------------------------------

record GeometricalOpticsAlgebra (Scalar : Set) : Set₁ where
  constructor geometrical-optics-algebra
  field
    zero one : Scalar
    add multiply divide subtract : Scalar → Scalar → Scalar
    sin : Scalar → Scalar
    reciprocal : Scalar → Scalar
    _≤_ : Scalar → Scalar → Set

open GeometricalOpticsAlgebra public

record SnellRefractionReceipt
    {Scalar : Set}
    (algebra : GeometricalOpticsAlgebra Scalar) : Set where
  constructor snell-refraction-receipt
  field
    incidentIndex : Scalar
    refractedIndex : Scalar
    incidentAngle : Scalar
    refractedAngle : Scalar
    snellLaw :
      multiply algebra incidentIndex (sin algebra incidentAngle)
      ≡ multiply algebra refractedIndex (sin algebra refractedAngle)

open SnellRefractionReceipt public

record CriticalAngleReceipt
    {Scalar : Set}
    (algebra : GeometricalOpticsAlgebra Scalar) : Set where
  constructor critical-angle-receipt
  field
    highIndex : Scalar
    lowIndex : Scalar
    criticalAngle : Scalar
    indexOrdering : _≤_ algebra lowIndex highIndex
    criticalBoundaryLaw :
      multiply algebra highIndex (sin algebra criticalAngle)
      ≡ lowIndex

open CriticalAngleReceipt public

record TotalInternalReflectionReceipt
    {Scalar : Set}
    (algebra : GeometricalOpticsAlgebra Scalar)
    (critical : CriticalAngleReceipt algebra) : Set where
  constructor total-internal-reflection-receipt
  field
    incidentAngle : Scalar
    atOrAboveCritical :
      _≤_ algebra (criticalAngle critical) incidentAngle

open TotalInternalReflectionReceipt public

------------------------------------------------------------------------
-- Prism dispersion retains n(lambda) explicitly.
------------------------------------------------------------------------

record PrismDispersionReceipt
    {Scalar Wavelength : Set}
    (algebra : GeometricalOpticsAlgebra Scalar) : Set₁ where
  constructor prism-dispersion-receipt
  field
    prismApexAngle : Scalar
    refractiveIndex : Wavelength → Scalar
    firstWavelength : Wavelength
    secondWavelength : Wavelength
    firstIndex : Scalar
    secondIndex : Scalar
    firstIndexLaw : firstIndex ≡ refractiveIndex firstWavelength
    secondIndexLaw : secondIndex ≡ refractiveIndex secondWavelength

open PrismDispersionReceipt public

------------------------------------------------------------------------
-- Thin-lens image formation and lens-maker receipts.
------------------------------------------------------------------------

record ThinLensReceipt
    {Scalar : Set}
    (algebra : GeometricalOpticsAlgebra Scalar) : Set where
  constructor thin-lens-receipt
  field
    focalLength : Scalar
    objectDistance : Scalar
    imageDistance : Scalar
    thinLensLaw :
      reciprocal algebra focalLength
      ≡ add algebra
          (reciprocal algebra objectDistance)
          (reciprocal algebra imageDistance)

open ThinLensReceipt public

record LensMakerReceipt
    {Scalar : Set}
    (algebra : GeometricalOpticsAlgebra Scalar) : Set where
  constructor lens-maker-receipt
  field
    refractiveIndex : Scalar
    firstRadius : Scalar
    secondRadius : Scalar
    focalLength : Scalar
    lensMakerLaw :
      reciprocal algebra focalLength
      ≡ multiply algebra
          (subtract algebra refractiveIndex (one algebra))
          (subtract algebra
            (reciprocal algebra firstRadius)
            (reciprocal algebra secondRadius))

open LensMakerReceipt public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data SnellReceiptIsFullWaveOptics : Set where
snellReceiptIsNotFullWaveOptics : SnellReceiptIsFullWaveOptics → ⊥
snellReceiptIsNotFullWaveOptics ()

data ThinLensReceiptDeterminesAberrations : Set where
thinLensReceiptDoesNotDetermineAberrations : ThinLensReceiptDeterminesAberrations → ⊥
thinLensReceiptDoesNotDetermineAberrations ()

data PrismDispersionDeterminesMaterialDispersionCurve : Set where
prismDispersionDoesNotDetermineMaterialDispersionCurve :
  PrismDispersionDeterminesMaterialDispersionCurve → ⊥
prismDispersionDoesNotDetermineMaterialDispersionCurve ()
