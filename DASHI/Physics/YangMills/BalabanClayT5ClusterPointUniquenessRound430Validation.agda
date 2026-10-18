{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5ClusterPointUniquenessRound430Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanClayT5ClusterPointUniquenessRound430Exact as R430
open import DASHI.Physics.YangMills.CompactLieProofLevel

clusterPointUniquenessCompilerMachineChecked :
  R430.round430ClusterPointUniquenessCompilerLevel ≡ machineChecked
clusterPointUniquenessCompilerMachineChecked = refl

clusterPointEqualityCompilerMachineChecked :
  R430.round430EveryExtractedClusterPointEqualityLevel ≡ machineChecked
clusterPointEqualityCompilerMachineChecked = refl

independentClusterPointEqualityPruned :
  R430.round430IndependentClusterPointEqualityInputRequired ≡ false
independentClusterPointEqualityPruned = refl
