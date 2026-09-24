module DASHI.Statistics.ForecastResolutionSelectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Statistics.ForecastVerificationKernelExact as Kernel

------------------------------------------------------------------------
-- FORECAST LIFECYCLE / SCORABILITY / TEMPORAL EVIDENCE CUT
--
-- A forecast, a later world event, a resolution judgement, and a scored row are
-- separate objects.  Retrospective evidence may be acquired after the forecast;
-- such evidence can explain what happened without being silently transported
-- into the information state available when the forecast was issued.
------------------------------------------------------------------------

data ForecastDomain : Set where
  conflict cyber energy geopolitical infrastructure macro market military
  political supplyChain otherDomain : ForecastDomain

data ForecastOrigin : Set where
  betEngine legacyDetector stateDerived unknownOrigin otherOrigin :
    ForecastOrigin

record PublishedForecast : Set where
  constructor published-forecast
  field
    forecastReference : String
    propositionReference : String
    issuedAtReference : String
    horizonReference : String
    probability : Kernel.Probability
    domain : ForecastDomain
    origin : ForecastOrigin
    modelReference : String
    sourceStateReference : String
    resolutionPolicyReference : String

open PublishedForecast public

data ResolutionDisposition : Set where
  stillOpen awaitingJudge resolvedScored resolvedVoided :
    ResolutionDisposition

record ResolutionEvidence : Set where
  constructor resolution-evidence
  field
    evidenceReference : String
    resolverReference : String
    judgedAtReference : String
    policyVersionReference : String
    evidenceSetReference : String

open ResolutionEvidence public

data ResolutionState : Set where
  open-resolution : ResolutionState
  awaiting-resolution : ResolutionState
  scored-resolution :
    Kernel.BinaryOutcome →
    ResolutionEvidence →
    ResolutionState
  void-resolution :
    String →
    ResolutionEvidence →
    ResolutionState

resolutionDisposition : ResolutionState → ResolutionDisposition
resolutionDisposition open-resolution = stillOpen
resolutionDisposition awaiting-resolution = awaitingJudge
resolutionDisposition (scored-resolution _ _) = resolvedScored
resolutionDisposition (void-resolution _ _) = resolvedVoided

record ResolutionRevisionReceipt : Set where
  constructor resolution-revision-receipt
  field
    forecastReference : String
    previousStateReference : String
    nextStateReference : String
    supersedesReference : String
    revisionEvidenceReference : String
    revisionPolicyReference : String
    revisionCreatesWorldEvent : Bool
    revisionCreatesWorldEventIsFalse : revisionCreatesWorldEvent ≡ false

open ResolutionRevisionReceipt public

record ResolvedScorableForecast : Set where
  constructor resolved-scorable-forecast
  field
    forecast : PublishedForecast
    outcome : Kernel.BinaryOutcome
    resolutionEvidence : ResolutionEvidence
    scoringEligibilityReference : String

open ResolvedScorableForecast public

toScoredForecast : ResolvedScorableForecast → Kernel.ScoredForecast
toScoredForecast row =
  Kernel.scored-forecast
    (forecastReference (forecast row))
    (propositionReference (forecast row))
    (probability (forecast row))
    (outcome row)
    (evidenceReference (resolutionEvidence row))

------------------------------------------------------------------------
-- First-class cohort selection.
------------------------------------------------------------------------

record ForecastCohort : Set₁ where
  constructor forecast-cohort
  field
    admits : ResolvedScorableForecast → Set
    cohortReference : String
    targetPopulationReference : String

open ForecastCohort public

record CohortSelectionReceipt (cohort : ForecastCohort) : Set₁ where
  constructor cohort-selection-receipt
  field
    excluded : ResolvedScorableForecast → Set
    partitionReference : String
    exclusionReasonReference : String
    targetPopulationArgumentReference : String

open CohortSelectionReceipt public

------------------------------------------------------------------------
-- Forecast-time epistemic cut.
------------------------------------------------------------------------

record ForecastEpistemicCut
    (Time EvidenceAtom : Set) : Set₁ where
  constructor forecast-epistemic-cut
  field
    forecastIssuedAt : Time
    availableAt : EvidenceAtom → Time
    _≤T_ : Time → Time → Set

    admissibleAtForecast : EvidenceAtom → Set

    admissibilitySound :
      (atom : EvidenceAtom) →
      admissibleAtForecast atom →
      availableAt atom ≤T forecastIssuedAt

    hindsightAtom : EvidenceAtom → Set
    sourceProvenanceReference : EvidenceAtom → String
    cutReference : String

open ForecastEpistemicCut public

record ForecastHindsightSeparation
    {Time EvidenceAtom : Set}
    (cut : ForecastEpistemicCut Time EvidenceAtom) : Set₁ where
  constructor forecast-hindsight-separation
  field
    lateAtom : EvidenceAtom
    knownInHindsight : hindsightAtom cut lateAtom
    notAdmissibleAtForecast : ¬ (admissibleAtForecast cut lateAtom)
    separationReference : String

open ForecastHindsightSeparation public

------------------------------------------------------------------------
-- Controlled score recomputation surface.
--
-- These are score-comparison coordinates, not causal effects.
------------------------------------------------------------------------

data ScoreRecomputationKind : Set where
  rawWindowDelta
  holdCohortRuleFixed
  holdResolvedIntersectionFixed
  holdOriginMixtureFixed
  holdDomainMixtureFixed
  holdResolutionObserverFixed :
    ScoreRecomputationKind

record ScoreRecomputation : Set where
  constructor score-recomputation
  field
    kind : ScoreRecomputationKind
    sourceSnapshotReference : String
    targetSnapshotReference : String
    controlledCoordinateReference : String
    sourceScoreReference : String
    targetScoreReference : String
    deltaReference : String
    causalAttributionClaimed : Bool
    causalAttributionClaimedIsFalse : causalAttributionClaimed ≡ false

open ScoreRecomputation public

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ForecastResolutionSelectionBoundary : Set where
  constructor forecast-resolution-selection-boundary
  field
    inLedgerMeansResolved : Bool
    inLedgerMeansResolvedIsFalse : inLedgerMeansResolved ≡ false

    resolvedMeansScored : Bool
    resolvedMeansScoredIsFalse : resolvedMeansScored ≡ false

    goodScoreOnScorableSubsetMeansIssuedPopulationSkill : Bool
    goodScoreOnScorableSubsetMeansIssuedPopulationSkillIsFalse :
      goodScoreOnScorableSubsetMeansIssuedPopulationSkill ≡ false

    hindsightEvidenceMayEnterForecastTimeCutSilently : Bool
    hindsightEvidenceMayEnterForecastTimeCutSilentlyIsFalse :
      hindsightEvidenceMayEnterForecastTimeCutSilently ≡ false

    resolutionJudgementIsWorldEvent : Bool
    resolutionJudgementIsWorldEventIsFalse :
      resolutionJudgementIsWorldEvent ≡ false

    controlledRecomputationIsCausalAttribution : Bool
    controlledRecomputationIsCausalAttributionIsFalse :
      controlledRecomputationIsCausalAttribution ≡ false

canonicalForecastResolutionSelectionBoundary :
  ForecastResolutionSelectionBoundary
canonicalForecastResolutionSelectionBoundary =
  forecast-resolution-selection-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
