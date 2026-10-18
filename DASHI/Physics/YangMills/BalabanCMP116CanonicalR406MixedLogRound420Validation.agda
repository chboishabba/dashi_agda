{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalR406MixedLogRound420Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanCMP116CanonicalR406MixedLogRound420Exact as R420
open import DASHI.Physics.YangMills.CompactLieProofLevel

r406MixedLogCompilerMachineChecked :
  R420.round420R406MixedLogCompilerLevel ≡ machineChecked
r406MixedLogCompilerMachineChecked = refl

noAdditionalCovarianceTheorem :
  R420.round420AdditionalCovarianceTheoremRequired ≡ false
noAdditionalCovarianceTheorem = refl
