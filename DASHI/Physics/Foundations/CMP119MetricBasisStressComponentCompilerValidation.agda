{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119MetricBasisStressComponentCompilerValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Foundations.CMP119MetricBasisStressComponentCompilerExact as C

noSecondStressRepresentation :
  C.secondStressRepresentationNeededForComponents ≡ false
noSecondStressRepresentation = refl

basisIdentificationStillPhysical :
  C.metricBasis16StillNeedsPhysicalCoordinateIdentification ≡ true
basisIdentificationStillPhysical = refl
