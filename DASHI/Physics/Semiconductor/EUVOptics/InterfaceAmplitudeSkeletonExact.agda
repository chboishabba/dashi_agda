{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.EUVOptics.InterfaceAmplitudeSkeletonExact where

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Exact finite skeleton for an interface coefficient.  Real EUV optics needs
-- complex refractive indices and complex amplitudes; this owner only provides
-- a division-free relation suitable for later refinement.

record InterfaceCoordinates : Set where
  constructor interfaceCoordinates
  field
    incidentIndexCode : Nat
    transmittedIndexCode : Nat
    numeratorCode : Nat
    denominatorCode : Nat

open InterfaceCoordinates public

-- Algebraic shape corresponding to a normal-incidence Fresnel-style ratio
-- r = (n1 - n2)/(n1 + n2), represented only through supplied numerator and
-- denominator codes.  We deliberately do not define Nat subtraction here.
record InterfaceAmplitudeWitness (x : InterfaceCoordinates) : Set where
  constructor interfaceAmplitudeWitness
  field
    numeratorPlusTransmittedTwice : numeratorCode x + (2 * transmittedIndexCode x) ≡ incidentIndexCode x + transmittedIndexCode x
    denominatorEquation : denominatorCode x ≡ incidentIndexCode x + transmittedIndexCode x

open InterfaceAmplitudeWitness public

syntheticInterface : InterfaceCoordinates
syntheticInterface = interfaceCoordinates 5 3 2 8

syntheticInterfaceWitness : InterfaceAmplitudeWitness syntheticInterface
syntheticInterfaceWitness = interfaceAmplitudeWitness refl refl

-- The same index pair can participate in different physical interfaces once
-- absorption, roughness, polarization and angle are admitted.  Thus this finite
-- skeleton must not be promoted directly to EUV reflectivity.
data OpticalResidual : Set where
  ComplexIndexRealPart : OpticalResidual
  ComplexIndexImaginaryPart : OpticalResidual
  IncidenceAngle : OpticalResidual
  PolarizationState : OpticalResidual
  InterfaceRoughness : OpticalResidual
  InterdiffusionWidth : OpticalResidual
  ThermalDistortion : OpticalResidual
