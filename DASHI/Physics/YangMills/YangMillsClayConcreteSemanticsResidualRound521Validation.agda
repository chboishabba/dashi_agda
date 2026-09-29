{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayConcreteSemanticsResidualRound521Validation where
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.YangMills.YangMillsClayConcreteSemanticsResidualRound521Exact as R521
open import DASHI.Physics.YangMills.CompactLieProofLevel
analysisCount : R521.sourceAnalysisLeafCount ≡ 15
analysisCount = refl
attachmentCount : R521.sourceLiteralAttachmentLeafCount ≡ 16
attachmentCount = refl
addedSourceCount : R521.addedSourceLeafCount ≡ 2
addedSourceCount = refl
endpointCount : R521.endpointSemanticLeafCount ≡ 0
endpointCount = refl
residualCount : R521.residualLeafCount ≡ 33
residualCount = refl
compiler : R521.round521ConcreteSemanticsResidualCompilerLevel ≡ machineChecked
compiler = refl
