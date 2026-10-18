{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119SingleActiveSectorSourceFactorisationValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Foundations.CMP119SingleActiveSectorSourceFactorisationExact as C

compilerOwned :
  C.singleSectorCompilerLevel ≡ machineChecked
compilerOwned = refl

declaredTotalNotManufactured :
  C.singleSectorCompilerDoesNotManufactureDeclaredTotal ≡ false
declaredTotalNotManufactured = refl
