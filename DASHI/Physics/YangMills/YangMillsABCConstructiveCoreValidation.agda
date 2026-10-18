{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsABCConstructiveCoreValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsABCConstructiveCoreExact as ABC

abcCompilerOwned :
  ABC.abcConstructiveCoreCompilerLevel ≡ machineChecked
abcCompilerOwned = refl
