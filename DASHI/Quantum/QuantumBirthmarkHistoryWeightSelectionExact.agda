{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkHistoryWeightSelectionExact where

open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.Foundations.ContextConditionedTrajectoryWeightExact as Context
import DASHI.Physics.Foundations.HistoryWeightFiltrationExact as Filtration

------------------------------------------------------------------------
-- BIRTHMARK-CONDITIONED HISTORY WEIGHTING
--
-- A birthmark is allowed to act as context for selecting/reweighting an already
-- admissible history family.  This is deliberately weaker than identifying a
-- birthmark statistic with a Gibbs weight, a quantum phase, or an MDL prior.
------------------------------------------------------------------------

record BirthmarkHistoryWeightSelection : Set₁ where
  field
    BirthmarkRecord : Set
    History : Set
    Weight : Set

    admissibleHistory : History → Set
    historyWeight : BirthmarkRecord → History → Weight

    selectedBirthmark : BirthmarkRecord
    selectedHistory : History
    selectedHistoryAdmissible : admissibleHistory selectedHistory

open BirthmarkHistoryWeightSelection public

record BirthmarkContextWeightChange
    (selection : BirthmarkHistoryWeightSelection) : Set₁ where
  field
    comparisonBirthmark : BirthmarkRecord selection
    WeightDifference : Set
    weightDifferenceEvidence : WeightDifference

open BirthmarkContextWeightChange public

------------------------------------------------------------------------
-- Semantic firewall inherited from the existing history-weight filtration.
------------------------------------------------------------------------

birthmarkWeightIsGibbsWeightByDefinition : Bool
birthmarkWeightIsGibbsWeightByDefinition = false

birthmarkWeightIsQuantumPhaseByDefinition : Bool
birthmarkWeightIsQuantumPhaseByDefinition = false

birthmarkWeightIsMDLPriorByDefinition : Bool
birthmarkWeightIsMDLPriorByDefinition = false

contextReweightingChangesUnderlyingLawAutomatically : Bool
contextReweightingChangesUnderlyingLawAutomatically = false

birthmarkCanConditionHistorySelectionWithoutErasingAdmissibility : Bool
birthmarkCanConditionHistorySelectionWithoutErasingAdmissibility = true

microscopicBirthmarkWeightLawStillRequired : Bool
microscopicBirthmarkWeightLawStillRequired = true

normalizationAndQuantumAmplitudeRuleStillRequired : Bool
normalizationAndQuantumAmplitudeRuleStillRequired = true
