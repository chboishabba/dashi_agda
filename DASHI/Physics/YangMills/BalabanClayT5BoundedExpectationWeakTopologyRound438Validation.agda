{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5BoundedExpectationWeakTopologyRound438Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanClayT5BoundedExpectationWeakTopologyRound438Exact as R438
open import DASHI.Physics.YangMills.CompactLieProofLevel

boundedWeakTopologyCompilerMachineChecked :
  R438.round438BoundedWeakTopologyCompilerLevel ≡ machineChecked
boundedWeakTopologyCompilerMachineChecked = refl

expectationContinuityIsDefinitional :
  R438.round438ExpectationContinuityByDefinitionLevel ≡ machineChecked
expectationContinuityIsDefinitional = refl

clusterPointUniquenessCompilerMachineChecked :
  R438.round438ClusterPointUniquenessCompilerLevel ≡ machineChecked
clusterPointUniquenessCompilerMachineChecked = refl

independentMeasureContinuityPruned :
  R438.round438IndependentMeasureContinuityTheoremRequired ≡ false
independentMeasureContinuityPruned = refl
