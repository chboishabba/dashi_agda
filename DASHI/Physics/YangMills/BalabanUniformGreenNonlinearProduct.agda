module DASHI.Physics.YangMills.BalabanUniformGreenNonlinearProduct where

------------------------------------------------------------------------
-- Exact quantifier form of the constructive background-field hinge
--
--   sup_{Λ,k,U₀,P} C_G(Λ,k,U₀,P) L_N(Λ,k,U₀,P) ≤ ρ_G < 1.
--
-- Rather than introducing a real-valued supremum unnecessarily, the theorem
-- uses its order-theoretic content: one common rho bounds every indexed
-- product.  The analytic work is the construction of the fields below; the
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
