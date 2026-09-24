{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5SelectedWeakTopologyMeaningRound435Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanClayT5SelectedWeakTopologyMeaningRound435Exact as R435
open import DASHI.Physics.YangMills.CompactLieProofLevel

selectedWeakTopologyCompilerMachineChecked :
  R435.round435SelectedWeakTopologyCompilerLevel ≡ machineChecked
selectedWeakTopologyCompilerMachineChecked = refl

determiningAuthorityCompilerMachineChecked :
  R435.round435R430DeterminingAuthorityCompilerLevel ≡ machineChecked
determiningAuthorityCompilerMachineChecked = refl

independentClusterAgreementPruned :
  R435.round435IndependentClusterPointAgreementRequired ≡ false
independentClusterAgreementPruned = refl
