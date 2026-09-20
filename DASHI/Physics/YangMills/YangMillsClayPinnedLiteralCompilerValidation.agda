module DASHI.Physics.YangMills.YangMillsClayPinnedLiteralCompilerValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayPinnedLiteralCompilerExact as P

literalCompilerOwned :
  P.pinnedLiteralClayCompilerLevel ≡ machineChecked
literalCompilerOwned = refl

interactingContinuumRemainsPhysical :
  P.pinnedInteractingContinuumInputLevel ≡ conditional
interactingContinuumRemainsPhysical = refl
