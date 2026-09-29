{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsSourceFirstWilsonCovarianceRound556Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonCovarianceRound556Exact as R556
open import DASHI.Physics.YangMills.CompactLieProofLevel

covarianceLimitCompilerMachineChecked :
  R556.round556SameFamilyCovarianceConvergenceCompilerLevel ≡ machineChecked
covarianceLimitCompilerMachineChecked = refl

carrierSelectionMachineChecked :
  R556.round556WEXTCarrierIsExactSelectedCovarianceLevel ≡ machineChecked
carrierSelectionMachineChecked = refl

noSeparateConvergenceLeaf :
  R556.separateSameFamilyWilsonCovarianceConvergenceLeafRequired ≡ false
noSeparateConvergenceLeaf = refl

noPrintedJ :
  R556.printedJPresentationRequired ≡ false
noPrintedJ = refl
