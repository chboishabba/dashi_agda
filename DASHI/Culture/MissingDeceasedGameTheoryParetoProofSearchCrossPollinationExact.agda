module DASHI.Culture.MissingDeceasedGameTheoryParetoProofSearchCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import DASHI.Algebra.BalancedTernary using (zero)

import DASHI.Dynamics.TernaryLifeGame as Ternary
import DASHI.GameTheory.StrategicInteractionCoreExact as Game
import DASHI.Core.ReferencePopulationRosterEnrichmentExact as Stats
import DASHI.Core.NDimParetoHyperfabricExact as Pareto
import DASHI.Core.ProofSearchExperimentalParetoCrossPollinationExact as Search
import DASHI.Culture.MissingDeceasedTernaryAdversarialObserverExact as Observer
import DASHI.Culture.ChineseStrategicScientistRosterSnowballExact as China

------------------------------------------------------------------------
-- GAME THEORY x STATISTICS x PARETO x PROOF SEARCH
--
-- The ternary observer states are search perspectives, not diagnoses or players
-- known to exist historically.  Strategic models may nominate discriminating
-- acquisitions; game payoff never becomes evidence, and equilibrium never
-- becomes historical prediction.  Statistical enrichment requires a denominator
-- and predeclared matched controls.  Pareto remains non-scalarised.
------------------------------------------------------------------------

existingStrategicBoundary : Game.StrategicInteractionBoundary
existingStrategicBoundary = Game.canonicalStrategicInteractionBoundary

existingEnrichmentBoundary : Stats.EnrichmentBoundary
existingEnrichmentBoundary = Stats.canonicalEnrichmentBoundary

existingParetoBoundary : Pareto.NDimParetoHyperfabricBoundary
existingParetoBoundary = Pareto.canonicalNDimParetoHyperfabricBoundary

existingProofSearchParetoBoundary : Search.ProofSearchExperimentalParetoBoundary
existingProofSearchParetoBoundary = Search.canonicalProofSearchExperimentalParetoBoundary

existingTernaryRule : Ternary.Rule
existingTernaryRule = Ternary.evolvingRule zero

record InvestigativeSearchAxis : Set where
  constructor investigative-search-axis
  field
    axisName : String
    axisMeaning : String
    lowerIsOperationallyPreferred : Bool
    evidenceAuthorityCreatedByAxis : Bool

open InvestigativeSearchAxis public

identityDebtAxis : InvestigativeSearchAxis
identityDebtAxis = investigative-search-axis
  "identity/same-object debt"
  "unpaid person, manifestation, programme or same-object welds"
  true false

primarySourceDebtAxis : InvestigativeSearchAxis
primarySourceDebtAxis = investigative-search-axis
  "primary-source debt"
  "distance from event/work claim to authoritative source class"
  true false

controlDebtAxis : InvestigativeSearchAxis
controlDebtAxis = investigative-search-axis
  "matched-control / denominator debt"
  "missing reference population or predeclared matched controls"
  true false

causalBridgeDebtAxis : InvestigativeSearchAxis
causalBridgeDebtAxis = investigative-search-axis
  "causal-bridge debt"
  "distance between paid technical kernel and claimed common-cause mechanism"
  true false

adversarialDiscriminationDebtAxis : InvestigativeSearchAxis
adversarialDiscriminationDebtAxis = investigative-search-axis
  "adversarial-discrimination debt"
  "failure of a hypothesis to predict an observation different from ordinary/control explanations"
  true false

acquisitionCostAxis : InvestigativeSearchAxis
acquisitionCostAxis = investigative-search-axis
  "acquisition cost"
  "source-class/access/implementation burden of the next discriminating object"
  true false

------------------------------------------------------------------------
-- Proof-search proposals bind acquisition to live residuals without turning
-- source reconstruction into theorem authority.
------------------------------------------------------------------------

chinesePrimaryWorkProposal : Search.FrontierRefinementProposal
chinesePrimaryWorkProposal = Search.frontierRefinementProposal
  Search.sourceReconstruction
  "Chinese strategic-scientist roster: work-identity and event-identity residuals"
  "cross-national cohort comparator"
  "identity debt + primary-source debt + causal-bridge debt"
  "replace media field labels with source-attributed work objects and isolate remaining event/same-person gaps"
  "person/work/event same-object receipts remain explicit per roster row"
  "source reconstruction may refine the frontier but does not establish a cross-national common cause"

uapDiscriminatorProposal : Search.FrontierRefinementProposal
uapDiscriminatorProposal = Search.frontierRefinementProposal
  Search.sourceReconstruction
  "UAP/Area-51 paid-kernel -> missing-bridge residual"
  "UAP/adversarial hypothesis discriminator"
  "causal-bridge debt + matched-control debt + adversarial-discrimination debt"
  "prune self-sealing narratives; retain only claims with independent predicted observables"
  "technical science object and alleged covert programme object must be independently welded"
  "hypothesis-guided acquisition only; no theorem/evidence promotion from strategic plausibility"

------------------------------------------------------------------------
-- Ternary perspective routing over time.
------------------------------------------------------------------------

record PerspectiveSearchPolicy : Set where
  constructor perspective-search-policy
  field
    perspective : Observer.ObserverPolarity
    firstQuestion : String
    preferredCountercheck : String
    canCloseEvidenceLeafByPerspectiveAlone : Bool

open PerspectiveSearchPolicy public

patternPolicy : PerspectiveSearchPolicy
patternPolicy = perspective-search-policy
  Observer.patternDetector
  "what conjunction or dependency is easiest to miss under a high-specificity search?"
  "matched controls and denominator-aware enrichment"
  false

baselinePolicy : PerspectiveSearchPolicy
baselinePolicy = perspective-search-policy
  Observer.baselineObserver
  "what do literal event/work sources establish before any common-cause model?"
  "same-object provenance and ordinary reference population"
  false

adversarialPolicy : PerspectiveSearchPolicy
adversarialPolicy = perspective-search-policy
  Observer.adversarialObserver
  "what observable would a competent concealment/selection process leave that an ordinary process would not?"
  "chronology, pre-public tasking, access/custody linkage and falsifiable counterprediction"
  false

------------------------------------------------------------------------
-- Statistics/game/Pareto firewalls.
------------------------------------------------------------------------

gamePayoffDoesNotBecomeEvidence : Bool
gamePayoffDoesNotBecomeEvidence = true

equilibriumDoesNotPredictCohortHistory : Bool
equilibriumDoesNotPredictCohortHistory = true

rosterFrequencyWithoutDenominatorIsNotEnrichment : Bool
rosterFrequencyWithoutDenominatorIsNotEnrichment = true

paretoDoesNotRequireScalarConspiracyScore : Bool
paretoDoesNotRequireScalarConspiracyScore = true

primaryWorkAcquisitionMayPrecedeEventWeld : Bool
primaryWorkAcquisitionMayPrecedeEventWeld = true

record GameStatsParetoSearchBoundary : Set where
  constructor game-stats-pareto-search-boundary
  field
    strategicPlausibilityCreatesEvidence : Bool
    posteriorOrPayoffMayReplacePrimarySource : Bool
    matchedControlsRequiredForEnrichment : Bool
    paretoScalarisationRequired : Bool
    proofSearchMayUseHypothesisToChooseAcquisition : Bool
    proofSearchMaySkipIdentityDependency : Bool

canonicalGameStatsParetoSearchBoundary : GameStatsParetoSearchBoundary
canonicalGameStatsParetoSearchBoundary = game-stats-pareto-search-boundary
  false false true false true false
