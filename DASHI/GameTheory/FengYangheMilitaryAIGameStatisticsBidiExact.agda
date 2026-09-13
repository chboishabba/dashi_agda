module DASHI.GameTheory.FengYangheMilitaryAIGameStatisticsBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.GameTheory.StrategicInteractionCoreExact as Game
import DASHI.Core.ReferencePopulationRosterEnrichmentExact as Stats

------------------------------------------------------------------------
-- FENG YANGHE / MILITARY AI, WARGAMING AND STATISTICAL CLASSIFICATION
--
-- Primary NUDT sources describe the War Skull II intelligent wargame agent,
-- task-level autonomous decision making, adversarial red/blue play, and Feng as
-- team leader.  NUDT Press separately attributes Bayesian classification and
-- noisy-label machine-learning books to Feng Yanghe and coauthors.
------------------------------------------------------------------------

data FengWorkFamily : Set where
  intelligentWargameAgent multiGroupBayesianClassification noisyLabelClassification : FengWorkFamily

record FengWorkReceipt : Set where
  constructor feng-work-receipt
  field
    family : FengWorkFamily
    workObject : String
    method : String
    application : String
    sourceReference : String
    sourceClass : String
    primaryInstitutional : Bool

open FengWorkReceipt public

warSkullIIReceipt : FengWorkReceipt
warSkullIIReceipt = feng-work-receipt
  intelligentWargameAgent
  "War Skull II / NUDT-Agent intelligent wargaming system"
  "task-level autonomous decision modules; joint air defence, anti-surface and air-combat modules; opponent-adaptive tactic selection"
  "red/blue military wargame simulation and intelligent command/decision support"
  "National University of Defense Technology, 2020-12-29, War Skull II intelligent-game report"
  "primary institutional research/news page"
  true

bayesianClassificationReceipt : FengWorkReceipt
bayesianClassificationReceipt = feng-work-receipt
  multiGroupBayesianClassification
  "Introduction to Multi-group Graph Bayesian Classification Models"
  "Bayesian theorem; multinomial/Dirichlet assumptions; sampling; automatic filtering of noisy/redundant attributes; regression/classification"
  "statistical classification"
  "NUDT Press ISBN 978-7-5673-0533-5, 2019"
  "primary institutional publisher catalogue"
  true

noisyLabelClassificationReceipt : FengWorkReceipt
noisyLabelClassificationReceipt = feng-work-receipt
  noisyLabelClassification
  "Machine Learning Classification Methods under Noisy Labels"
  "classification under label noise"
  "robust machine learning"
  "NUDT Press ISBN 978-7-5673-0611-0, 2023"
  "primary institutional publisher catalogue"
  true

------------------------------------------------------------------------
-- Existing game/statistics semantics are imported rather than replaced.
------------------------------------------------------------------------

existingStrategicBoundary : Game.StrategicInteractionBoundary
existingStrategicBoundary = Game.canonicalStrategicInteractionBoundary

existingEnrichmentBoundary : Stats.EnrichmentBoundary
existingEnrichmentBoundary = Stats.canonicalEnrichmentBoundary

record FengCrossPollinationBoundary : Set where
  constructor feng-cross-pollination-boundary
  field
    wargameAgentImpliesRealWorldHistoricalPrediction : Bool
    gamePayoffEqualsStatisticalEvidence : Bool
    noisyLabelRobustnessEliminatesSelectionBias : Bool
    bayesianModelImpliesBayesianEvidenceForCohortHypothesis : Bool
    strategicMethodsMayNominateAdversarialTests : Bool
    matchedControlsStillRequiredForRosterEnrichment : Bool

canonicalFengCrossPollinationBoundary : FengCrossPollinationBoundary
canonicalFengCrossPollinationBoundary = feng-cross-pollination-boundary
  false false false false true true
