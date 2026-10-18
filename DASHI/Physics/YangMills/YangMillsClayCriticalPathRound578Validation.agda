{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCriticalPathRound578Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayCriticalPathRound578Exact as R578
open import DASHI.Physics.YangMills.CompactLieProofLevel

criticalFamilyCountIsSeven :
  R578.criticalFamilyCount ≡ 7
criticalFamilyCountIsSeven = refl

noArbitraryObservableRepresentation :
  R578.arbitraryObservableRepresentationRequired ≡ false
noArbitraryObservableRepresentation = refl

noFiniteHamiltonianMoscoDetour :
  R578.finiteHamiltonianMoscoRouteRequired ≡ false
noFiniteHamiltonianMoscoDetour = refl

noPrintedJWilsonIdentification :
  R578.printedJEqualsWilsonRequired ≡ false
noPrintedJWilsonIdentification = refl

noSU2Promotion :
  R578.su2ToGenericPromotionRequired ≡ false
noSU2Promotion = refl

criticalPathCompilerMachineChecked :
  R578.round578CriticalPathCompilerLevel ≡ machineChecked
criticalPathCompilerMachineChecked = refl
