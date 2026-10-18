module DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact as P

constructionCompilerOwned :
  P.pinnedPhysicalConstructionCompilerLevel ≡ machineChecked
constructionCompilerOwned = refl

t78ACompilerOwned :
  P.pinnedT78ACompilerLevel ≡ machineChecked
t78ACompilerOwned = refl

t78BCompilerOwned :
  P.pinnedT78BCompilerLevel ≡ machineChecked
t78BCompilerOwned = refl

t78CCompilerOwned :
  P.pinnedT78CCompilerLevel ≡ machineChecked
t78CCompilerOwned = refl

siAttachmentCompilerOwned :
  P.pinnedSIGapAttachmentCompilerLevel ≡ machineChecked
siAttachmentCompilerOwned = refl

physicalInputsRemainPhysical :
  P.pinnedPhysicalInputsLevel ≡ conditional
physicalInputsRemainPhysical = refl
