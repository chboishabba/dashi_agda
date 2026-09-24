{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119SymmetricPresentCutMetricBasisCompilerValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Foundations.CMP119SymmetricPresentCutMetricBasisCompilerExact as C

finiteTangentMapNotPrimitive :
  C.separateComponentToFiniteTangentMapRequired ≡ false
finiteTangentMapNotPrimitive = refl

metricBasisMapNotPrimitive :
  C.separateComponentToMetricBasisMapRequired ≡ false
metricBasisMapNotPrimitive = refl
