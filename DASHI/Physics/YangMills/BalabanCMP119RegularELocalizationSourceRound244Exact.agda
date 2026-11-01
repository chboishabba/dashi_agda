{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119RegularELocalizationSourceRound244Exact where

------------------------------------------------------------------------
-- ROUND244 / CMP119 REGULAR-E LOCALIZATION: SOURCE THEOREM != CARRIER WELD
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFunctionalRegularESourceFlowRound242Exact as R242
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite

record CMP119RegularELocalizationCarrier
    {trajectory split inputs}
    (source : R242.FunctionalRegularESourceFlowInputs
      {trajectory = trajectory} {split = split} inputs) : Set₁ where
  field
    Volume Component : Set

    components : Nat → Volume → List Component

    localizedRegularActivity :
      Nat → Volume → Component → R242.Background source → ℝ

    -- Literal CMP119 (2.25)--(2.27) representation on the exact selected E_k.
    selectedRegularEIsLocalizedCompositeSum :
      ∀ scale volume background →
      R242.selectedRegularEFunction source scale background
      ≡ Finite.sumFunctions
          (Finite.mapList
            (localizedRegularActivity scale volume)
            (components scale volume))
          background

open CMP119RegularELocalizationCarrier public

-- CMP119 Sect.2 (2.25)--(2.29) is the source theorem providing this localized
-- representation, analyticity/locality/gauge invariance and inherited bounds.
cmp119RegularELocalizationSourceLevel : ProofLevel
cmp119RegularELocalizationSourceLevel = standardImported

-- Remaining source/repository realization: instantiate the literal source's
-- localization domains and activity functions so the printed equality above is
-- an equality on our exact function-valued regular-E/background carrier.
literalCMP119RegularELocalizationCarrierLevel : ProofLevel
literalCMP119RegularELocalizationCarrierLevel = conditional
