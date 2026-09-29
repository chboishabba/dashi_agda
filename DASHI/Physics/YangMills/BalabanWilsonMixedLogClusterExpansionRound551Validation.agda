{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanWilsonMixedLogClusterExpansionRound551Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanWilsonMixedLogClusterExpansionRound551Exact as R551
open import DASHI.Physics.YangMills.CompactLieProofLevel

covarianceCompilerMachineChecked :
  R551.round551WilsonCovarianceExpansionCompilerLevel ≡ machineChecked
covarianceCompilerMachineChecked = refl

noSecondPhysicalCovarianceIdentity :
  R551.round551SecondPhysicalCovarianceIdentityRequired ≡ false
noSecondPhysicalCovarianceIdentity = refl

noPrintedJPromotion :
  R551.round551PrintedBalabanJEqualsWilsonObservableRequired ≡ false
noPrintedJPromotion = refl
