module DASHI.Physics.YangMills.BalabanPatchRegimeGreenUniformity where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPatchRegimeHodgeUniformity using
  (PatchRegime; bulk; boundary; scaleInterface; corner; nestedRestriction)

------------------------------------------------------------------------
-- Regimewise reference Green estimates assembled into one common weighted
-- bound. This is the B3 analogue of patch-regime Hodge uniformity.
------------------------------------------------------------------------

record PatchRegimeGreenData (Index State Bound : Set) : Set₁ where
  field
    regime : Index → PatchRegime
    green gradientGreen secondGradientGreen : Index → State → State
    weightedNorm : State → Bound
    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    multiplyMonotoneLeft : ∀ {left right} value →
      LessEqual left right →
      LessEqual (multiply left value) (multiply right value)

    bulkGreen boundaryGreen interfaceGreen cornerGreen nestedGreen
      commonGreen : Bound
    bulkGradient boundaryGradient interfaceGradient cornerGradient
      nestedGradient commonGradient : Bound
    bulkSecond boundarySecond interfaceSecond cornerSecond nestedSecond
      commonSecond : Bound

    bulkGreenBelowCommon : LessEqual bulkGreen commonGreen
    boundaryGreenBelowCommon : LessEqual boundaryGreen commonGreen
    interfaceGreenBelowCommon : LessEqual interfaceGreen commonGreen
    cornerGreenBelowCommon : LessEqual cornerGreen commonGreen
    nestedGreenBelowCommon : LessEqual nestedGreen commonGreen

    bulkGradientBelowCommon : LessEqual bulkGradient commonGradient
    boundaryGradientBelowCommon : LessEqual boundaryGradient commonGradient
    interfaceGradientBelowCommon : LessEqual interfaceGradient commonGradient
    cornerGradientBelowCommon : LessEqual cornerGradient commonGradient
    nestedGradientBelowCommon : LessEqual nestedGradient commonGradient

    bulkSecondBelowCommon : LessEqual bulkSecond commonSecond
    boundarySecondBelowCommon : LessEqual boundarySecond commonSecond
    interfaceSecondBelowCommon : LessEqual interfaceSecond commonSecond
    cornerSecondBelowCommon : LessEqual cornerSecond commonSecond
    nestedSecondBelowCommon : LessEqual nestedSecond commonSecond

    bulkBounds : ∀ index source → regime index ≡ bulk →
      LessEqual (weightedNorm (green index source))
        (multiply bulkGreen (weightedNorm source)) ×
      (LessEqual (weightedNorm (gradientGreen index source))
        (multiply bulkGradient (weightedNorm source)) ×
      LessEqual (weightedNorm (secondGradientGreen index source))
        (multiply bulkSecond (weightedNorm source)))

    boundaryBounds : ∀ index source → regime index ≡ boundary →
      LessEqual (weightedNorm (green index source))
        (multiply boundaryGreen (weightedNorm source)) ×
      (LessEqual (weightedNorm (gradientGreen index source))
        (multiply boundaryGradient (weightedNorm source)) ×
      LessEqual (weightedNorm (secondGradientGreen index source))
        (multiply boundarySecond (weightedNorm source)))

    interfaceBounds : ∀ index source → regime index ≡ scaleInterface →
      LessEqual (weightedNorm (green index source))
        (multiply interfaceGreen (weightedNorm source)) ×
      (LessEqual (weightedNorm (gradientGreen index source))
        (multiply interfaceGradient (weightedNorm source)) ×
      LessEqual (weightedNorm (secondGradientGreen index source))
        (multiply interfaceSecond (weightedNorm source)))

    cornerBounds : ∀ index source → regime index ≡ corner →
      LessEqual (weightedNorm (green index source))
        (multiply cornerGreen (weightedNorm source)) ×
      (LessEqual (weightedNorm (gradientGreen index source))
        (multiply cornerGradient (weightedNorm source)) ×
      LessEqual (weightedNorm (secondGradientGreen index source))
        (multiply cornerSecond (weightedNorm source)))

    nestedBounds : ∀ index source → regime index ≡ nestedRestriction →
      LessEqual (weightedNorm (green index source))
        (multiply nestedGreen (weightedNorm source)) ×
      (LessEqual (weightedNorm (gradientGreen index source))
        (multiply nestedGradient (weightedNorm source)) ×
      LessEqual (weightedNorm (secondGradientGreen index source))
        (multiply nestedSecond (weightedNorm source)))

    regimeComplete : ∀ index →
      (regime index ≡ bulk) ⊎
      (regime index ≡ boundary) ⊎
      (regime index ≡ scaleInterface) ⊎
      (regime index ≡ corner) ⊎
      (regime index ≡ nestedRestriction)

open PatchRegimeGreenData public

record CommonGreenBounds {Index State Bound : Set}
    (dataSet : PatchRegimeGreenData Index State Bound) : Set₁ where
  field
    greenBound : ∀ index source →
      LessEqual dataSet (weightedNorm dataSet (green dataSet index source))
        (multiply dataSet (commonGreen dataSet) (weightedNorm dataSet source))
    gradientBound : ∀ index source →
      LessEqual dataSet (weightedNorm dataSet (gradientGreen dataSet index source))
        (multiply dataSet (commonGradient dataSet) (weightedNorm dataSet source))
    secondGradientBound : ∀ index source →
      LessEqual dataSet (weightedNorm dataSet (secondGradientGreen dataSet index source))
        (multiply dataSet (commonSecond dataSet) (weightedNorm dataSet source))

open CommonGreenBounds public

assembleCommonGreenBounds :
  ∀ {Index State Bound : Set} →
  (dataSet : PatchRegimeGreenData Index State Bound) →
  CommonGreenBounds dataSet
assembleCommonGreenBounds dataSet = record
  { greenBound = greenCommon
  ; gradientBound = gradientCommon
  ; secondGradientBound = secondCommon
  }
  where
  promote : ∀ {local common value source} →
    LessEqual dataSet local common →
    LessEqual dataSet value (multiply dataSet local (weightedNorm dataSet source)) →
    LessEqual dataSet value (multiply dataSet common (weightedNorm dataSet source))
  promote local≤common localBound =
    transitive dataSet localBound
      (multiplyMonotoneLeft dataSet _ local≤common)

  greenCommon : ∀ index source →
    LessEqual dataSet (weightedNorm dataSet (green dataSet index source))
      (multiply dataSet (commonGreen dataSet) (weightedNorm dataSet source))
  greenCommon index source with regimeComplete dataSet index
  ... | inj₁ p = promote (bulkGreenBelowCommon dataSet)
      (proj₁ (bulkBounds dataSet index source p))
  ... | inj₂ (inj₁ p) = promote (boundaryGreenBelowCommon dataSet)
      (proj₁ (boundaryBounds dataSet index source p))
  ... | inj₂ (inj₂ (inj₁ p)) = promote (interfaceGreenBelowCommon dataSet)
      (proj₁ (interfaceBounds dataSet index source p))
  ... | inj₂ (inj₂ (inj₂ (inj₁ p))) = promote (cornerGreenBelowCommon dataSet)
      (proj₁ (cornerBounds dataSet index source p))
  ... | inj₂ (inj₂ (inj₂ (inj₂ p))) = promote (nestedGreenBelowCommon dataSet)
      (proj₁ (nestedBounds dataSet index source p))

  gradientCommon : ∀ index source →
    LessEqual dataSet (weightedNorm dataSet (gradientGreen dataSet index source))
      (multiply dataSet (commonGradient dataSet) (weightedNorm dataSet source))
  gradientCommon index source with regimeComplete dataSet index
  ... | inj₁ p = promote (bulkGradientBelowCommon dataSet)
      (proj₁ (proj₂ (bulkBounds dataSet index source p)))
  ... | inj₂ (inj₁ p) = promote (boundaryGradientBelowCommon dataSet)
      (proj₁ (proj₂ (boundaryBounds dataSet index source p)))
  ... | inj₂ (inj₂ (inj₁ p)) = promote (interfaceGradientBelowCommon dataSet)
      (proj₁ (proj₂ (interfaceBounds dataSet index source p)))
  ... | inj₂ (inj₂ (inj₂ (inj₁ p))) = promote (cornerGradientBelowCommon dataSet)
      (proj₁ (proj₂ (cornerBounds dataSet index source p)))
  ... | inj₂ (inj₂ (inj₂ (inj₂ p))) = promote (nestedGradientBelowCommon dataSet)
      (proj₁ (proj₂ (nestedBounds dataSet index source p)))

  secondCommon : ∀ index source →
    LessEqual dataSet (weightedNorm dataSet (secondGradientGreen dataSet index source))
      (multiply dataSet (commonSecond dataSet) (weightedNorm dataSet source))
  secondCommon index source with regimeComplete dataSet index
  ... | inj₁ p = promote (bulkSecondBelowCommon dataSet)
      (proj₂ (proj₂ (bulkBounds dataSet index source p)))
  ... | inj₂ (inj₁ p) = promote (boundarySecondBelowCommon dataSet)
      (proj₂ (proj₂ (boundaryBounds dataSet index source p)))
  ... | inj₂ (inj₂ (inj₁ p)) = promote (interfaceSecondBelowCommon dataSet)
      (proj₂ (proj₂ (interfaceBounds dataSet index source p)))
  ... | inj₂ (inj₂ (inj₂ (inj₁ p))) = promote (cornerSecondBelowCommon dataSet)
      (proj₂ (proj₂ (cornerBounds dataSet index source p)))
  ... | inj₂ (inj₂ (inj₂ (inj₂ p))) = promote (nestedSecondBelowCommon dataSet)
      (proj₂ (proj₂ (nestedBounds dataSet index source p)))

patchRegimeGreenAssemblyLevel : ProofLevel
patchRegimeGreenAssemblyLevel = machineChecked

patchRegimeGreenEstimateInputsLevel : ProofLevel
patchRegimeGreenEstimateInputsLevel = conditional
