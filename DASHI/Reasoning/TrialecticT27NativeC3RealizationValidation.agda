module DASHI.Reasoning.TrialecticT27NativeC3RealizationValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TrialecticT27NativeC3RealizationExact as Native

boundary : Native.TrialecticT27NativeC3RealizationBoundary
boundary = Native.canonicalTrialecticT27NativeC3RealizationBoundary

policyInhabited : Native.nativeC3PolicyInhabited boundary ≡ true
policyInhabited = refl

sheafInhabited : Native.nativeC3GraphSheafInhabited boundary ≡ true
sheafInhabited = refl

groupoidInhabited : Native.nativeC3WavePhaseGroupoidInhabited boundary ≡ true
groupoidInhabited = refl

higherStackInhabited : Native.nativeC3HigherStackInhabited boundary ≡ true
higherStackInhabited = refl

finiteHypersheafInhabited : Native.nativeC3FiniteHypersheafInhabited boundary ≡ true
finiteHypersheafInhabited = refl

notPhysical : Native.nativeC3StructuralPolicyIsPhysicalDynamics boundary ≡ false
notPhysical = refl

notIIT : Native.nativeC3PolicyEqualsIITBOperatorPolicy boundary ≡ false
notIIT = refl

receipt : Native.NativeC3T27Realization
receipt = Native.canonicalNativeC3T27Realization
