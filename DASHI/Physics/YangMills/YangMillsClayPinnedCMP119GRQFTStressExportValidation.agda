{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119GRQFTStressExportValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119GRQFTStressExportExact as Export

exportIsMachineChecked :
  Export.pinnedCMP119GRQFTStressExportLevel ≡ machineChecked
exportIsMachineChecked = refl

sharedGRQFTCarrierNotImported :
  Export.importsGRQFTSharedCarrier ≡ false
sharedGRQFTCarrierNotImported = refl
