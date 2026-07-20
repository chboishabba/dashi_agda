module DASHI.Physics.YangMills.BalabanPatchRegimeHodgeUniformity where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Uniform reference coercivity across the five patch regimes which occur in
-- the multiscale Green construction.
------------------------------------------------------------------------

data PatchRegime : Set where
  bulk boundary scaleInterface corner nestedRestriction : PatchRegime

record PatchRegimeHodgeData (Index State Bound : Set) : Set₁ where
  field
    regime : Index → PatchRegime
    energy normSq : Index → State → Bound
    scale : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    bulkConstant boundaryConstant interfaceConstant cornerConstant
      nestedConstant commonConstant : Bound

    commonBelowBulk : ∀ index state →
      LessEqual (scale commonConstant (normSq index state))
        (scale bulkConstant (normSq index state))
    commonBelowBoundary : ∀ index state →
      LessEqual (scale commonConstant (normSq index state))
        (scale boundaryConstant (normSq index state))
    commonBelowInterface : ∀ index state →
      LessEqual (scale commonConstant (normSq index state))
        (scale interfaceConstant (normSq index state))
    commonBelowCorner : ∀ index state →
      LessEqual (scale commonConstant (normSq index state))
        (scale cornerConstant (normSq index state))
    commonBelowNested : ∀ index state →
      LessEqual (scale commonConstant (normSq index state))
        (scale nestedConstant (normSq index state))

    bulkHodge : ∀ index state → regime index ≡ bulk →
      LessEqual (scale bulkConstant (normSq index state)) (energy index state)
    boundaryHodge : ∀ index state → regime index ≡ boundary →
      LessEqual (scale boundaryConstant (normSq index state)) (energy index state)
    interfaceHodge : ∀ index state → regime index ≡ scaleInterface →
      LessEqual (scale interfaceConstant (normSq index state)) (energy index state)
    cornerHodge : ∀ index state → regime index ≡ corner →
      LessEqual (scale cornerConstant (normSq index state)) (energy index state)
    nestedHodge : ∀ index state → regime index ≡ nestedRestriction →
      LessEqual (scale nestedConstant (normSq index state)) (energy index index state)

    regimeComplete : ∀ index →
      (regime index ≡ bulk) ⊎
      (regime index ≡ boundary) ⊎
      (regime index ≡ scaleInterface) ⊎
      (regime index ≡ corner) ⊎
      (regime index ≡ nestedRestriction)

    Positive : Bound → Set
    commonPositive : Positive commonConstant

open PatchRegimeHodgeData public

uniformPatchHodge :
  ∀ {Index State Bound : Set} →
  (dataSet : PatchRegimeHodgeData Index State Bound) →
  ∀ index state →
  LessEqual dataSet
    (scale dataSet (commonConstant dataSet) (normSq dataSet index state))
    (energy dataSet index state)
uniformPatchHodge dataSet index state with regimeComplete dataSet index
... | inj₁ bulkCase =
  transitive dataSet
    (commonBelowBulk dataSet index state)
    (bulkHodge dataSet index state bulkCase)
... | inj₂ (inj₁ boundaryCase) =
  transitive dataSet
    (commonBelowBoundary dataSet index state)
    (boundaryHodge dataSet index state boundaryCase)
... | inj₂ (inj₂ (inj₁ interfaceCase)) =
  transitive dataSet
    (commonBelowInterface dataSet index state)
    (interfaceHodge dataSet index state interfaceCase)
... | inj₂ (inj₂ (inj₂ (inj₁ cornerCase))) =
  transitive dataSet
    (commonBelowCorner dataSet index state)
    (cornerHodge dataSet index state cornerCase)
... | inj₂ (inj₂ (inj₂ (inj₂ nestedCase))) =
  transitive dataSet
    (commonBelowNested dataSet index state)
    (nestedHodge dataSet index state nestedCase)

patchRegimeHodgeAssemblyLevel : ProofLevel
patchRegimeHodgeAssemblyLevel = machineChecked

patchRegimeHodgeEstimateInputsLevel : ProofLevel
patchRegimeHodgeEstimateInputsLevel = conditional
