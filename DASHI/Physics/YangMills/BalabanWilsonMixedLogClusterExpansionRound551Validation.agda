{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanWilsonMixedLogClusterExpansionRound551Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanWilsonMixedLogClusterExpansionExact as R551
open import DASHI.Physics.YangMills.CompactLieProofLevel

covarianceCompilerMachineChecked :
  R551.wilsonCovarianceExpansionCompilerLevel ≡ machineChecked
covarianceCompilerMachineChecked = refl

noSecondPhysicalCovarianceIdentity :
  R551.secondPhysicalCovarianceIdentityRequired ≡ false
noSecondPhysicalCovarianceIdentity = refl

noPrintedJPromotion :
  R551.printedBalabanJEqualsWilsonObservableRequired ≡ false
noPrintedJPromotion = refl
