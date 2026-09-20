module DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalInstanceValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalInstanceExact as P

physicalProjectionCompilerOwned :
  P.physicalPinnedProjectionCompilerLevel ≡ machineChecked
physicalProjectionCompilerOwned = refl
