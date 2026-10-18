module DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalGapAttachmentValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalGapAttachmentExact as P

clusteringAttachmentCompilerOwned :
  P.pinnedPhysicalClusteringAttachmentCompilerLevel ≡ machineChecked
clusteringAttachmentCompilerOwned = refl

siRateAttachmentCompilerOwned :
  P.pinnedSIPhysicalRateAttachmentCompilerLevel ≡ machineChecked
siRateAttachmentCompilerOwned = refl

uniformClusteringRemainsPhysical :
  P.pinnedUniformPhysicalClusteringInputLevel ≡ conditional
uniformClusteringRemainsPhysical = refl
