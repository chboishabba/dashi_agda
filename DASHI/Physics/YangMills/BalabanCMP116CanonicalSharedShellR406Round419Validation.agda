{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalSharedShellR406Round419Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanCMP116CanonicalSharedShellR406Round419Exact as R419
open import DASHI.Physics.YangMills.CompactLieProofLevel

canonicalSharedShellCompilerMachineChecked :
  R419.round419CanonicalSharedShellR406CompilerLevel ≡ machineChecked
canonicalSharedShellCompilerMachineChecked = refl

postHocBShellEqualityPruned :
  R419.round419PostHocBShellEqualityRequired ≡ false
postHocBShellEqualityPruned = refl
