{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCriticalPathRound562Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayCriticalPathRound562Exact as R562
open import DASHI.Physics.YangMills.CompactLieProofLevel

criticalFamilyCountIsSeven :
  R562.criticalFamilyCount ≡ 7
criticalFamilyCountIsSeven = refl

a3LimitIntegralCompilerOwned :
  R562.a3SelectedLimitIntegralCompilerLevel ≡ machineChecked
a3LimitIntegralCompilerOwned = refl

w1CovarianceCompilerOwned :
  R562.w1CovarianceIdentityCompilerLevel ≡ machineChecked
w1CovarianceCompilerOwned = refl

oldR499RoutePruned :
  R562.oldR499AllObservableRouteRequired ≡ false
oldR499RoutePruned = refl

noProkhorov :
  R562.prokhorovRouteRequired ≡ false
noProkhorov = refl

criticalPathCompilerMachineChecked :
  R562.round562CriticalPathCompilerLevel ≡ machineChecked
criticalPathCompilerMachineChecked = refl
