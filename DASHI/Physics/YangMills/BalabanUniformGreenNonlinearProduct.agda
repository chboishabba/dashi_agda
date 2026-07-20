module DASHI.Physics.YangMills.BalabanUniformGreenNonlinearProduct where

------------------------------------------------------------------------
-- Exact quantifier form of the constructive background-field hinge
--
--   sup_{Λ,k,U₀,P} C_G(Λ,k,U₀,P) L_N(Λ,k,U₀,P) ≤ ρ_G < 1.
--
-- Rather than introducing a real-valued supremum unnecessarily, the theorem
-- uses its order-theoretic content: one common rho bounds every indexed
-- product. The analytic work is the construction of the fields below; the
-- passage to a uniform residual contraction is checked here.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.CompactLieYangMillsFrontier as Frontier

record BalabanPatchIndex
    (Volume Scale Background Patch : Set) : Set where
  constructor balabanIndex
  field
    volume : Volume
    scale : Scale
    background : Background
    patch : Patch

open BalabanPatchIndex public

record UniformGreenNonlinearProduct
    (Volume Scale Background Patch State Bound : Set) : Set₁ where
  field
    residual : BalabanPatchIndex Volume Scale Background Patch → State → State
    norm : State → Bound

    greenConstant : BalabanPatchIndex Volume Scale Background Patch → Bound
    nonlinearConstant : BalabanPatchIndex Volume Scale Background Patch → Bound
    rhoG : Bound

    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    StrictlyBelowOne : Bound → Set

    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    multiplyMonotoneLeft : ∀ suffix {left right} →
      LessEqual left right →
      LessEqual (multiply left suffix) (multiply right suffix)

    rhoGStrict : StrictlyBelowOne rhoG

    greenNonlinearProductBound : ∀ index →
      LessEqual
        (multiply (greenConstant index) (nonlinearConstant index))
        rhoG

    localResidualEstimate : ∀ index state →
      LessEqual
        (norm (residual index state))
        (multiply
          (multiply (greenConstant index) (nonlinearConstant index))
          (norm state))

open UniformGreenNonlinearProduct public

-- A frequently useful stronger input shape: the Green and nonlinear constants
-- have separate uniform upper bounds and only the product of those two common
-- bounds must be compared with rhoG.
record SeparatedUniformGreenNonlinearBounds
    (Volume Scale Background Patch State Bound : Set) : Set₁ where
  field
    residual : BalabanPatchIndex Volume Scale Background Patch → State → State
    norm : State → Bound

    greenConstant : BalabanPatchIndex Volume Scale Background Patch → Bound
    nonlinearConstant : BalabanPatchIndex Volume Scale Background Patch → Bound
    greenUpper : Bound
    nonlinearUpper : Bound
    rhoG : Bound

    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    StrictlyBelowOne : Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    multiplyMonotone : ∀ {left left′ right right′} →
      LessEqual left left′ → LessEqual right right′ →
      LessEqual (multiply left right) (multiply left′ right′)
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

open SeparatedUniformGreenNonlinearBounds public

separatedProductBound :
  ∀ {Volume Scale Background Patch State Bound : Set} →
  (dataSet :
    SeparatedUniformGreenNonlinearBounds
      Volume Scale Background Patch State Bound) →
  ∀ index →
  SeparatedUniformGreenNonlinearBounds.LessEqual dataSet
    (SeparatedUniformGreenNonlinearBounds.multiply dataSet
      (SeparatedUniformGreenNonlinearBounds.greenConstant dataSet index)
      (SeparatedUniformGreenNonlinearBounds.nonlinearConstant dataSet index))
    (SeparatedUniformGreenNonlinearBounds.rhoG dataSet)
separatedProductBound dataSet index =
  SeparatedUniformGreenNonlinearBounds.transitive dataSet
    (SeparatedUniformGreenNonlinearBounds.multiplyMonotone dataSet
      (SeparatedUniformGreenNonlinearBounds.greenUniform dataSet index)
      (SeparatedUniformGreenNonlinearBounds.nonlinearUniform dataSet index))
    (SeparatedUniformGreenNonlinearBounds.upperProductBelowRho dataSet)

fromSeparatedUniformBounds :
  ∀ {Volume Scale Background Patch State Bound : Set} →
  SeparatedUniformGreenNonlinearBounds
    Volume Scale Background Patch State Bound →
  UniformGreenNonlinearProduct
    Volume Scale Background Patch State Bound
fromSeparatedUniformBounds dataSet = record
  { residual = SeparatedUniformGreenNonlinearBounds.residual dataSet
  ; norm = SeparatedUniformGreenNonlinearBounds.norm dataSet
  ; greenConstant = SeparatedUniformGreenNonlinearBounds.greenConstant dataSet
  ; nonlinearConstant = SeparatedUniformGreenNonlinearBounds.nonlinearConstant dataSet
  ; rhoG = SeparatedUniformGreenNonlinearBounds.rhoG dataSet
  ; multiply = SeparatedUniformGreenNonlinearBounds.multiply dataSet
  ; LessEqual = SeparatedUniformGreenNonlinearBounds.LessEqual dataSet
  ; StrictlyBelowOne = SeparatedUniformGreenNonlinearBounds.StrictlyBelowOne dataSet
  ; transitive = SeparatedUniformGreenNonlinearBounds.transitive dataSet
  ; multiplyMonotoneLeft =
      SeparatedUniformGreenNonlinearBounds.multiplyMonotoneLeft dataSet
  ; rhoGStrict = SeparatedUniformGreenNonlinearBounds.rhoGStrict dataSet
  ; greenNonlinearProductBound = separatedProductBound dataSet
  ; localResidualEstimate =
      SeparatedUniformGreenNonlinearBounds.localResidualEstimate dataSet
  }

uniformResidualEstimate :
  ∀ {Volume Scale Background Patch State Bound : Set} →
  (dataSet :
    UniformGreenNonlinearProduct
      Volume Scale Background Patch State Bound) →
  ∀ index state →
  LessEqual dataSet
    (norm dataSet (residual dataSet index state))
    (multiply dataSet (rhoG dataSet) (norm dataSet state))
uniformResidualEstimate dataSet index state =
  transitive dataSet
    (localResidualEstimate dataSet index state)
    (multiplyMonotoneLeft dataSet (norm dataSet state)
      (greenNonlinearProductBound dataSet index))

toUniformResidualContractionTarget :
  ∀ {Volume Scale Background Patch State Bound : Set} →
  UniformGreenNonlinearProduct
    Volume Scale Background Patch State Bound →
  Frontier.UniformResidualContractionTarget
    (BalabanPatchIndex Volume Scale Background Patch) State Bound
toUniformResidualContractionTarget dataSet = record
  { residual = residual dataSet
  ; norm = norm dataSet
  ; rho = rhoG dataSet
  ; StrictlyBelowOne = StrictlyBelowOne dataSet
  ; LessEqual = LessEqual dataSet
  ; multiply = multiply dataSet
  ; rhoStrict = rhoGStrict dataSet
  ; uniformContraction = uniformResidualEstimate dataSet
  }

uniformGreenNonlinearBridgeLevel : ProofLevel
uniformGreenNonlinearBridgeLevel = machineChecked

uniformGreenNonlinearAnalyticInputsLevel : ProofLevel
uniformGreenNonlinearAnalyticInputsLevel = conjectural
