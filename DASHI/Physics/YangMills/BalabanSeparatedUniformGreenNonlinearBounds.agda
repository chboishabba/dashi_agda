module DASHI.Physics.YangMills.BalabanSeparatedUniformGreenNonlinearBounds where

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanUniformGreenNonlinearProduct as Uniform

record SeparatedUniformBounds
    (Volume Scale Background Patch State Bound : Set) : Set₁ where
  field
    residual : Uniform.BalabanPatchIndex Volume Scale Background Patch → State → State
    norm : State → Bound
    greenConstant : Uniform.BalabanPatchIndex Volume Scale Background Patch → Bound
    nonlinearConstant : Uniform.BalabanPatchIndex Volume Scale Background Patch → Bound
    greenUpper : Bound
    nonlinearUpper : Bound
    rhoG : Bound
    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    StrictlyBelowOne : Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    multiplyMonotone : ∀ {left leftPrime right rightPrime} →
      LessEqual left leftPrime → LessEqual right rightPrime →
      LessEqual (multiply left right) (multiply leftPrime rightPrime)
    multiplyMonotoneLeft : ∀ suffix {left right} →
      LessEqual left right →
      LessEqual (multiply left suffix) (multiply right suffix)
    greenUniform : ∀ index → LessEqual (greenConstant index) greenUpper
    nonlinearUniform : ∀ index →
      LessEqual (nonlinearConstant index) nonlinearUpper
    upperProductBelowRho : LessEqual (multiply greenUpper nonlinearUpper) rhoG
    rhoGStrict : StrictlyBelowOne rhoG
    localResidualEstimate : ∀ index state →
      LessEqual
        (norm (residual index state))
        (multiply
          (multiply (greenConstant index) (nonlinearConstant index))
          (norm state))

separatedProductBound :
  ∀ {Volume Scale Background Patch State Bound : Set} →
  (dataSet : SeparatedUniformBounds
    Volume Scale Background Patch State Bound) →
  ∀ index →
  SeparatedUniformBounds.LessEqual dataSet
    (SeparatedUniformBounds.multiply dataSet
      (SeparatedUniformBounds.greenConstant dataSet index)
      (SeparatedUniformBounds.nonlinearConstant dataSet index))
    (SeparatedUniformBounds.rhoG dataSet)
separatedProductBound dataSet index =
  SeparatedUniformBounds.transitive dataSet
    (SeparatedUniformBounds.multiplyMonotone dataSet
      (SeparatedUniformBounds.greenUniform dataSet index)
      (SeparatedUniformBounds.nonlinearUniform dataSet index))
    (SeparatedUniformBounds.upperProductBelowRho dataSet)

toUniformGreenNonlinearProduct :
  ∀ {Volume Scale Background Patch State Bound : Set} →
  (dataSet : SeparatedUniformBounds
    Volume Scale Background Patch State Bound) →
  Uniform.UniformGreenNonlinearProduct
    Volume Scale Background Patch State Bound
toUniformGreenNonlinearProduct dataSet = record
  { residual = SeparatedUniformBounds.residual dataSet
  ; norm = SeparatedUniformBounds.norm dataSet
  ; greenConstant = SeparatedUniformBounds.greenConstant dataSet
  ; nonlinearConstant = SeparatedUniformBounds.nonlinearConstant dataSet
  ; rhoG = SeparatedUniformBounds.rhoG dataSet
  ; multiply = SeparatedUniformBounds.multiply dataSet
  ; LessEqual = SeparatedUniformBounds.LessEqual dataSet
  ; StrictlyBelowOne = SeparatedUniformBounds.StrictlyBelowOne dataSet
  ; transitive = SeparatedUniformBounds.transitive dataSet
  ; multiplyMonotoneLeft = SeparatedUniformBounds.multiplyMonotoneLeft dataSet
  ; rhoGStrict = SeparatedUniformBounds.rhoGStrict dataSet
  ; greenNonlinearProductBound = separatedProductBound dataSet
  ; localResidualEstimate = SeparatedUniformBounds.localResidualEstimate dataSet
  }

separatedUniformBoundsBridgeLevel : ProofLevel
separatedUniformBoundsBridgeLevel = machineChecked

separatedGreenAndNonlinearInputsLevel : ProofLevel
separatedGreenAndNonlinearInputsLevel = conjectural
