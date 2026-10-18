{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119LiteralStressAttachmentValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119LiteralStressAttachmentExact as A

compilerOwned :
  A.pinnedCMP119LiteralStressAttachmentCompilerLevel ≡ machineChecked
compilerOwned = refl

nameDoesNotManufactureSameObject :
  A.sameObjectAttachmentManufacturedFromPinnedName ≡ false
nameDoesNotManufactureSameObject = refl
