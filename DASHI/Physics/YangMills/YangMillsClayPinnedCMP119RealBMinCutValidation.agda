{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealBMinCutValidation where

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealBMinCutExact as B
open import DASHI.Physics.YangMills.CompactLieProofLevel

postCoordinateCompilerIsMachineChecked :
  B.pinnedCMP119RealBPostCoordinateCompilerLevel ≡ machineChecked
postCoordinateCompilerIsMachineChecked = refl

selectedJCoordinateRemainsPhysical :
  B.pinnedCMP119RealBSelectedJCoordinateLevel ≡ conditional
selectedJCoordinateRemainsPhysical = refl

selectedEnvelopeRemainsPhysical :
  B.pinnedCMP119RealBSelectedEnvelopeLevel ≡ conditional
selectedEnvelopeRemainsPhysical = refl
