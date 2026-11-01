module DASHI.Physics.YangMills.BalabanReferenceGreenPerturbation where

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanBackgroundFieldClosure as Background

record ReferenceGreenPerturbationData
    (Index State Bound : Set) : Set₁ where
  field
    correctionInverse : Index → State → State
    referenceGreen : Index → State → State
    referenceGradientGreen : Index → State → State
    referenceSecondGradientGreen : Index → State → State
    weightedNorm : Bound → State → Bound
    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    multiplyMonotoneLeft : ∀ prefix {left right} →
      LessEqual left right →
      LessEqual (multiply prefix left) (multiply prefix right)
    reassociateUpper : ∀ left middle right →
      LessEqual (multiply left (multiply middle right))
        (multiply (multiply left middle) right)
    muG correctionUpper referenceUpper
      referenceGradientUpper referenceSecondGradientUpper : Bound
    correctionInverseBound : ∀ index source →
      LessEqual
        (weightedNorm muG (correctionInverse index source))
        (multiply correctionUpper (weightedNorm muG source))
    referenceGreenBound : ∀ index source →
      LessEqual
        (weightedNorm muG (referenceGreen index source))
        (multiply referenceUpper (weightedNorm muG source))
    referenceGradientGreenBound : ∀ index source →
      LessEqual
        (weightedNorm muG (referenceGradientGreen index source))
        (multiply referenceGradientUpper (weightedNorm muG source))
    referenceSecondGradientGreenBound : ∀ index source →
      LessEqual
        (weightedNorm muG (referenceSecondGradientGreen index source))
        (multiply referenceSecondGradientUpper (weightedNorm muG source))

open ReferenceGreenPerturbationData public

fullGreen :
  ∀ {Index State Bound : Set} →
  ReferenceGreenPerturbationData Index State Bound →
  Index → State → State
fullGreen dataSet index source =
  referenceGreen dataSet index (correctionInverse dataSet index source)

fullGradientGreen :
  ∀ {Index State Bound : Set} →
  ReferenceGreenPerturbationData Index State Bound →
  Index → State → State
fullGradientGreen dataSet index source =
  referenceGradientGreen dataSet index
    (correctionInverse dataSet index source)

fullSecondGradientGreen :
  ∀ {Index State Bound : Set} →
  ReferenceGreenPerturbationData Index State Bound →
  Index → State → State
fullSecondGradientGreen dataSet index source =
  referenceSecondGradientGreen dataSet index
    (correctionInverse dataSet index source)

composedBound :
  ∀ {Index State Bound : Set} →
  (dataSet : ReferenceGreenPerturbationData Index State Bound) →
  (operator : Index → State → State) →
  (operatorUpper : Bound) →
  (operatorBound : ∀ index source →
    LessEqual dataSet
      (weightedNorm dataSet (muG dataSet) (operator index source))
      (multiply dataSet operatorUpper
        (weightedNorm dataSet (muG dataSet) source))) →
  ∀ index source →
  LessEqual dataSet
    (weightedNorm dataSet (muG dataSet)
      (operator index (correctionInverse dataSet index source)))
    (multiply dataSet
      (multiply dataSet operatorUpper (correctionUpper dataSet))
      (weightedNorm dataSet (muG dataSet) source))
composedBound dataSet operator operatorUpper operatorBound index source =
  transitive dataSet
    (operatorBound index (correctionInverse dataSet index source))
    (transitive dataSet
      (multiplyMonotoneLeft dataSet operatorUpper
        (correctionInverseBound dataSet index source))
      (reassociateUpper dataSet operatorUpper (correctionUpper dataSet)
        (weightedNorm dataSet (muG dataSet) source)))

toUniformWeightedGreenEstimates :
  ∀ {Index State Bound : Set} →
  (dataSet : ReferenceGreenPerturbationData Index State Bound) →
  Background.UniformWeightedGreenEstimates Index State Bound
toUniformWeightedGreenEstimates dataSet = record
  { green = fullGreen dataSet
  ; gradientGreen = fullGradientGreen dataSet
  ; secondGradientGreen = fullSecondGradientGreen dataSet
  ; weightedNorm = weightedNorm dataSet
  ; multiply = multiply dataSet
  ; LessEqual = LessEqual dataSet
  ; muG = muG dataSet
  ; greenUpper = multiply dataSet
      (referenceUpper dataSet) (correctionUpper dataSet)
  ; gradientGreenUpper = multiply dataSet
      (referenceGradientUpper dataSet) (correctionUpper dataSet)
  ; secondGradientGreenUpper = multiply dataSet
      (referenceSecondGradientUpper dataSet) (correctionUpper dataSet)
  ; uniformWeightedGreenBound =
      composedBound dataSet (referenceGreen dataSet)
        (referenceUpper dataSet) (referenceGreenBound dataSet)
  ; uniformWeightedGradientGreenBound =
      composedBound dataSet (referenceGradientGreen dataSet)
        (referenceGradientUpper dataSet)
        (referenceGradientGreenBound dataSet)
  ; uniformWeightedSecondGradientGreenBound =
      composedBound dataSet (referenceSecondGradientGreen dataSet)
        (referenceSecondGradientUpper dataSet)
        (referenceSecondGradientGreenBound dataSet)
  }

referenceGreenPerturbationBridgeLevel : ProofLevel
referenceGreenPerturbationBridgeLevel = machineChecked

correctionInverseAndReferenceBoundsLevel : ProofLevel
correctionInverseAndReferenceBoundsLevel = conditional
