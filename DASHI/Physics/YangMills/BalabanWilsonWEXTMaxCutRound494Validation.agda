{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanWilsonWEXTMaxCutRound494Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanWilsonWEXTMaxCutRound494Exact as R494
open import DASHI.Physics.YangMills.CompactLieProofLevel

compilerMachineChecked :
  R494.round494WEXTCompilerLevel ≡ machineChecked
compilerMachineChecked = refl

triangleMachineChecked :
  R494.round494FiniteTriangleLevel ≡ machineChecked
triangleMachineChecked = refl

finalWEXTNotPrimitive :
  R494.finalWEXTInequalityStoredAsPrimitive ≡ false
finalWEXTNotPrimitive = refl

noPrintedJWilsonEquality :
  R494.printedJEqualsWilsonObservableRequired ≡ false
noPrintedJWilsonEquality = refl

twoMarkExpansionPhysical :
  R494.twoMarkExpansionStillPhysical ≡ true
twoMarkExpansionPhysical = refl

weightTailPhysical :
  R494.absoluteConnectingWeightTailStillPhysical ≡ true
weightTailPhysical = refl
