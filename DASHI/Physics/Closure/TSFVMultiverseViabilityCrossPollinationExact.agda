module DASHI.Physics.Closure.TSFVMultiverseViabilityCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.FundamentalConstantViabilityFibreExact as Viability
import DASHI.Physics.Closure.TSFVHistoryConditionedChoiceBridgeExact as TSFV
import DASHI.Core.HistoryConditionedChoiceExact as History
import DASHI.Core.ActiveBidiDiscriminatorLoopExact as Bidi

------------------------------------------------------------------------
-- TSFV / MULTIVERSE / VIABILITY CROSS-POLLINATION
--
-- TSFV already carries an exact finite lesson: different fine histories may
-- share a present coarse projection while later history-sensitive consumers
-- require different choices.  This module transports only that information
-- geometry into cosmological parameter-space reasoning.
--
-- It does NOT assert that TSFV generates a multiverse, that parameter points
-- are universes, or that anthropic selection validates TSFV.  A parameter scan
-- is a counterfactual theory space unless an independent physical-realisation
-- receipt is supplied.
------------------------------------------------------------------------

data RealisationStatus : Set where
  counterfactualParameterPoint
  physicallyRealisedWorld
  realisationUnresolved
  : RealisationStatus

data SelectionReading : Set where
  noSelectionReading
  observerSelectionCandidate
  dynamicalAttractorCandidate
  historyConditionedCandidate
  : SelectionReading

record CosmologicalCandidate : Set where
  constructor cosmological-candidate
  field
    parameterReference : String
    viabilityReference : String
    realisation : RealisationStatus
    selectionReading : SelectionReading
    historyReference : String
    observerReference : String

viabilityBoundary : Viability.FundamentalConstantViabilityBoundary
viabilityBoundary = Viability.canonicalFundamentalConstantViabilityBoundary

tsfvBoundary : TSFV.TSFVHistoryConditionedChoiceBoundary
tsfvBoundary = TSFV.canonicalTSFVHistoryConditionedChoiceBoundary

historyBoundary : History.HistoryConditionedChoiceBoundary
historyBoundary = History.canonicalHistoryConditionedChoiceBoundary

activeBidiBoundary : Bidi.ActiveBidiDiscriminatorLoopBoundary
activeBidiBoundary = Bidi.canonicalActiveBidiDiscriminatorLoopBoundary

record TSFVMultiverseViabilityBoundary : Set where
  constructor tsfv-multiverse-viability-boundary
  field
    parameterSpacePointIsAutomaticallyRealisedUniverse : Bool
    parameterSpacePointIsAutomaticallyRealisedUniverseIsFalse :
      parameterSpacePointIsAutomaticallyRealisedUniverse ≡ false
    viableParameterRegionProvesMultiverse : Bool
    viableParameterRegionProvesMultiverseIsFalse :
      viableParameterRegionProvesMultiverse ≡ false
    anthropicSelectionProvesTSFV : Bool
    anthropicSelectionProvesTSFVIsFalse : anthropicSelectionProvesTSFV ≡ false
    tsfvHistorySensitivityProvesCosmicParameterSelection : Bool
    tsfvHistorySensitivityProvesCosmicParameterSelectionIsFalse :
      tsfvHistorySensitivityProvesCosmicParameterSelection ≡ false
    samePresentCosmicObservablesNeedNotRecoverFineHistory : Bool
    samePresentCosmicObservablesNeedNotRecoverFineHistoryIsTrue :
      samePresentCosmicObservablesNeedNotRecoverFineHistory ≡ true
    observerConditioningAndDynamicalAttractorAreDistinctHypotheses : Bool
    observerConditioningAndDynamicalAttractorAreDistinctHypothesesIsTrue :
      observerConditioningAndDynamicalAttractorAreDistinctHypotheses ≡ true
    multiverseAttractorAndTSFVReadingsRequireSeparateDiscriminators : Bool
    multiverseAttractorAndTSFVReadingsRequireSeparateDiscriminatorsIsTrue :
      multiverseAttractorAndTSFVReadingsRequireSeparateDiscriminators ≡ true
    reading : String

canonicalTSFVMultiverseViabilityBoundary : TSFVMultiverseViabilityBoundary
canonicalTSFVMultiverseViabilityBoundary =
  tsfv-multiverse-viability-boundary
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    "TSFV contributes a history/projection non-factorability template to cosmological inference, not a multiverse theorem. Counterfactual parameter scans, observer-selection explanations, dynamical-attractor explanations and TSFV history-conditioned readings remain distinct live hypotheses until separate physical discriminators and realisation receipts are supplied."
