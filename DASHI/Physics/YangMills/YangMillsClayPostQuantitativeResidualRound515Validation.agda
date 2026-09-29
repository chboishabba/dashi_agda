{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPostQuantitativeResidualRound515Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayPostQuantitativeResidualRound515Exact as R515
open import DASHI.Physics.YangMills.CompactLieProofLevel

sourceAnalysisCountIsFifteen :
  R515.sourceAnalysisLeafCount ≡ 15
sourceAnalysisCountIsFifteen = refl

sourceAttachmentCountIsEighteen :
  R515.sourceLiteralAttachmentLeafCount ≡ 18
sourceAttachmentCountIsEighteen = refl

endpointSemanticCountIsTwentyOne :
  R515.endpointSemanticLeafCount ≡ 21
endpointSemanticCountIsTwentyOne = refl

residualCountIsFiftyFour :
  R515.residualLeafCount ≡ 54
residualCountIsFiftyFour = refl

finiteRegularityEstimateCompiled :
  R515.finiteRegularityAdditionalAnalysisStillResidual ≡ false
finiteRegularityEstimateCompiled = refl

finiteGrowthEstimateCompiled :
  R515.finiteGrowthAdditionalAnalysisStillResidual ≡ false
finiteGrowthEstimateCompiled = refl

sameFamilyAttachmentStillOpen :
  R515.quantitativeSameFamilyAttachmentStillResidual ≡ true
sameFamilyAttachmentStillOpen = refl

compilerMachineChecked :
  R515.round515PostQuantitativeResidualCompilerLevel ≡ machineChecked
compilerMachineChecked = refl
