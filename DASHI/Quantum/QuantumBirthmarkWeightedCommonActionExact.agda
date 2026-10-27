{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkWeightedCommonActionExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.CommonEffectiveActionVariationExact as Variation
import DASHI.Physics.Foundations.HistoryLocalActionAccumulationExact as Local
import DASHI.Quantum.QuantumBirthmarkHistoryWeightSelectionExact as Weight

------------------------------------------------------------------------
-- BIRTHMARK-CONDITIONED HISTORY -> EXISTING COMMON ACTION
--
-- The exact remaining adapter is one map from the birthmark-conditioned history
-- carrier to the history carrier already owned by CommonEffectiveActionVariation.
-- No independent stress tensor or second action is introduced.
------------------------------------------------------------------------

record BirthmarkWeightedCommonAction
    (U : Weld.UnifiedCandidate)
    (selection : Weight.BirthmarkHistoryWeightSelection)
    (variation : Variation.CommonEffectiveActionVariation U) : Set₁ where
  field
    historyToCommonActionHistory :
      Weight.History selection → Variation.History variation

    selectedCommonHistory : Variation.History variation

    selectedHistoryMapsExactly :
      historyToCommonActionHistory (Weight.selectedHistory selection)
      ≡ selectedCommonHistory

open BirthmarkWeightedCommonAction public

selectedBirthmarkHistoryAction :
  ∀ {U selection variation} →
  BirthmarkWeightedCommonAction U selection variation →
  Nat
selectedBirthmarkHistoryAction {variation = variation} bridge =
  Variation.finiteAction variation (selectedCommonHistory bridge)

selectedBirthmarkHistoryActionIsLiteralAccumulation :
  ∀ {U selection variation}
    (bridge : BirthmarkWeightedCommonAction U selection variation) →
  selectedBirthmarkHistoryAction bridge
  ≡
  Local.historyAction
    (Variation.localActionSystem variation)
    (Variation.historySteps variation (selectedCommonHistory bridge))
selectedBirthmarkHistoryActionIsLiteralAccumulation
    {variation = variation} bridge =
  Variation.finiteActionIsLiteralHistoryAction
    variation (selectedCommonHistory bridge)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

birthmarkSelectedHistoryToCommonActionCompilerOwned : Bool
birthmarkSelectedHistoryToCommonActionCompilerOwned = true

finiteHistoryActionAfterSelectionOwned : Bool
finiteHistoryActionAfterSelectionOwned = true

separateBirthmarkActionFunctionalRequired : Bool
separateBirthmarkActionFunctionalRequired = false

birthmarkHistorySelectionToCommonHistoryMapStillModelSpecific : Bool
birthmarkHistorySelectionToCommonHistoryMapStillModelSpecific = true

metricDependentEffectiveSourceStillModelSpecific : Bool
metricDependentEffectiveSourceStillModelSpecific = true
