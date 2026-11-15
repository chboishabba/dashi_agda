{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkHistoryCommonActionVariationExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.CommonEffectiveActionVariationExact as Variation
import DASHI.Physics.Foundations.CommonActionQFTGRVariationCompilerExact as Compiler
import DASHI.Physics.Foundations.EinsteinCommonActionVariationFrontierExact as EinsteinVariation
import DASHI.Physics.Foundations.BalabanCommonActionVariationFrontierExact as BalabanVariation
import DASHI.Physics.Foundations.HistoryLocalActionAccumulationExact as Local

------------------------------------------------------------------------
-- HISTORY -> COMMON EFFECTIVE ACTION -> SAME QFT/GR STRESS
--
-- CommonEffectiveActionVariation already owns the exact finite-history action
-- carrier and requires its finiteAction to be literally the accumulated local
-- history action.  Therefore the history-sector programme does not need a new
-- action formalism.  It only needs to instantiate that existing variation with
-- the physically selected history valuation/effective source.
------------------------------------------------------------------------

record BirthmarkHistoryCommonActionRealization
    (U : Weld.UnifiedCandidate) : Set₁ where
  field
    variation : Variation.CommonEffectiveActionVariation U
    selectedHistory : Variation.History variation

open BirthmarkHistoryCommonActionRealization public

selectedHistoryFiniteActionIsLiteralAccumulation :
  ∀ {U}
    (realization : BirthmarkHistoryCommonActionRealization U) →
  Variation.finiteAction (variation realization) (selectedHistory realization)
  ≡
  Local.historyAction
    (Variation.localActionSystem (variation realization))
    (Variation.historySteps (variation realization) (selectedHistory realization))
selectedHistoryFiniteActionIsLiteralAccumulation realization =
  Variation.finiteActionIsLiteralHistoryAction
    (variation realization) (selectedHistory realization)

------------------------------------------------------------------------
-- Existing common-action compiler consumes the same variation all the way to
-- a QFT/GR stress weld once the GR, QFT, and common metric-language receipts are
-- supplied.  No separate "history stress" tensor is introduced.
------------------------------------------------------------------------

historyCommonActionCompilesStressWeld :
  ∀ {U}
    (realization : BirthmarkHistoryCommonActionRealization U)
    (grReceipt :
      EinsteinVariation.EinsteinTensorVariationReceipt
        (variation realization))
    (qftReceipt :
      BalabanVariation.BalabanAllSectorVariationReceipt
        (variation realization))
    (commonLanguage : Compiler.CommonMetricVariationLanguage grReceipt qftReceipt) →
  Weld.StressEnergyWeldToken U →
  Weld.SameStressEnergyWeld U
historyCommonActionCompilesStressWeld realization grReceipt qftReceipt commonLanguage =
  Compiler.commonEinsteinAndBalabanVariationImpliesStressWeld
    (variation realization) grReceipt qftReceipt commonLanguage

------------------------------------------------------------------------
-- Max-cut boundary.
------------------------------------------------------------------------

finiteHistoryActionGenerationOwned : Bool
finiteHistoryActionGenerationOwned = true

finiteHistoryAdditivityOwned : Bool
finiteHistoryAdditivityOwned = true

commonMetricVariationStressCompilerOwned : Bool
commonMetricVariationStressCompilerOwned = true

separateHistoryStressTensorRequired : Bool
separateHistoryStressTensorRequired = false

microscopicBirthmarkToHistorySelectionStillRequired : Bool
microscopicBirthmarkToHistorySelectionStillRequired = true

physicalMetricDependentHistoryValuationStillRequired : Bool
physicalMetricDependentHistoryValuationStillRequired = true

continuumEffectiveSourceVariationStillModelSpecific : Bool
continuumEffectiveSourceVariationStillModelSpecific = true
