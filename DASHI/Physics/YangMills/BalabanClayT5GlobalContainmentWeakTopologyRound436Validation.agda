{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5GlobalContainmentWeakTopologyRound436Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanClayT5GlobalContainmentWeakTopologyRound436Exact as R436
open import DASHI.Physics.YangMills.CompactLieProofLevel

preferredCompactnessCompilerMachineChecked :
  R436.round436PreferredCompactnessCompilerLevel ≡ machineChecked
preferredCompactnessCompilerMachineChecked = refl

clusterPointEqualityCompilerOwned :
  R436.round436ClusterPointEqualityLevel ≡ machineChecked
clusterPointEqualityCompilerOwned = refl

independentUniquenessPruned :
  R436.round436IndependentUniquenessTheoremRequired ≡ false
independentUniquenessPruned = refl
