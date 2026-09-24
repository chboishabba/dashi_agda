{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.EinsteinFiniteToPhysicalCalibrationCompilerValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Closure.EinsteinFiniteToPhysicalCalibrationCompilerExact as C

finiteLawNotReproved :
  C.PhysicalEinsteinTransportBoundary.normalizedFiniteEquationNeedsReproofAfterCalibration
    C.canonicalPhysicalEinsteinTransportBoundary
  ≡ false
finiteLawNotReproved = refl

kappaOneDoesNotManufacturePhysicalScale :
  C.PhysicalEinsteinTransportBoundary.scaleCommutationCanBeInferredFromKappaOne
    C.canonicalPhysicalEinsteinTransportBoundary
  ≡ false
kappaOneDoesNotManufacturePhysicalScale = refl
