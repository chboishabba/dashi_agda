{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119SymmetricFiniteTangentBasisCompilerValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Foundations.CMP119SymmetricFiniteTangentBasisCompilerExact as C

directMetricMapNotPrimitive :
  C.directSymmetricSlotToCMP119MetricPerturbationIsPrimitive ≡ false
directMetricMapNotPrimitive = refl

finiteTangentBasisStillRequired :
  C.symmetricSlotToFiniteSourceTangentStillRequired ≡ true
finiteTangentBasisStillRequired = refl

r144TransportConsumed :
  C.r144TangentTransportReused ≡ true
r144TransportConsumed = refl
