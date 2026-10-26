module DASHI.Moonshine.Monster3BWZetaBasisVectorRecognitionCorrectionValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BWZetaBasisVectorRecognitionCorrectionExact as Cut

literalVOAStateCarrierKeptDistinctFromBasisLabels :
  Cut.literalVOAStateCarrierIsBasisLabelCarrier Cut.canonicalBoundary ≡ false
literalVOAStateCarrierKeptDistinctFromBasisLabels = refl

finiteModelIsBasisLabelSurface :
  Cut.finiteX6Fin90IsBasisLabelSurface Cut.canonicalBoundary ≡ true
finiteModelIsBasisLabelSurface = refl

basisRecognitionTargetTyped :
  Cut.actualBasisRecognitionTargetTyped Cut.canonicalBoundary ≡ true
basisRecognitionTargetTyped = refl

linearHomEvaluationTargetReused :
  Cut.linearHomEvaluationTargetReused Cut.canonicalBoundary ≡ true
linearHomEvaluationTargetReused = refl

oldWholeSectorBijectionNotRequired :
  Cut.wholeLiteralSectorBijectionToFiniteLabelsRequired Cut.canonicalBoundary ≡ false
oldWholeSectorBijectionNotRequired = refl

actualBasisRecognitionStillOpen :
  Cut.actualBasisRecognitionInhabitedHere Cut.canonicalBoundary ≡ false
actualBasisRecognitionStillOpen = refl

actualLinearHomSameObjectStillOpen :
  Cut.actualLinearHomSameObjectPaidHere Cut.canonicalBoundary ≡ false
actualLinearHomSameObjectStillOpen = refl
