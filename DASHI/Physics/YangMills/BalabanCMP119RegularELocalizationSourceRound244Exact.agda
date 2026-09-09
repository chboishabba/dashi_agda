{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119RegularELocalizationSourceRound244Exact where

------------------------------------------------------------------------
-- ROUND244 / CMP119 REGULAR-E LOCALIZATION: SOURCE THEOREM != CARRIER WELD
--
-- CMP119 Sect.2, especially (2.25)--(2.29), states that the regular E_k sector
-- has the localized representation inherited from the small-field effective
-- action.  Therefore the existence/locality/analyticity of that representation
-- is published source authority, not a new Clay estimate.
--
-- The repository still has to realize the source's localization domains and
-- local activity functions on the exact function-valued E_k/background carrier.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFunctionalRegularESourceFlowRound242Exact as R242

record CMP119RegularELocalizationCarrier
    {trajectory split inputs}
    (source : R242.FunctionalRegularESourceFlowInputs
      {trajectory = trajectory} {split = split} inputs) : Set₁ where
  field
    Volume Component : Set

    components : Nat → Volume → List Component

    localizedRegularActivity :
      Nat → Volume → Component → R242.Background source → ℝ

    -- This predicate is the repository interpretation of the literal CMP119
    -- (2.25)--(2.27) localized representation on this exact source carrier.
    IsLiteralCMP119RegularELocalization :
      Nat → Volume →
      (R242.Background source → ℝ) →
      List Component →
      (Component → R242.Background source → ℝ) → Set

    selectedLocalizationIsLiteral : ∀ scale volume →
      IsLiteralCMP119RegularELocalization scale volume
        (R242.selectedRegularEFunction source scale)
        (components scale volume)
        (localizedRegularActivity scale volume)

open CMP119RegularELocalizationCarrier public

-- Published source authority: CMP119 (2.25)--(2.29) supplies the regular-E
-- localized analytic representation and its locality/gauge/covariance content.
cmp119RegularELocalizationSourceLevel : ProofLevel
cmp119RegularELocalizationSourceLevel = standardImported

-- Remaining repository/source weld: instantiate the literal CMP119 localization
-- domains/components and local activity functions on the exact selected E_k
-- function carrier above.
literalCMP119RegularELocalizationCarrierLevel : ProofLevel
literalCMP119RegularELocalizationCarrierLevel = conditional
