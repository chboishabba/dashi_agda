module DASHI.Biology.AnimalexicLexicRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.SufficientSupportFamilyInvalidationExact as Support
import DASHI.Core.ProvenanceClosureIndependenceExact as Provenance
import DASHI.Core.AffectedDependencyClosureExact as Closure
import DASHI.Core.ExperimentLanguageEquivalenceExact as Experiment
import DASHI.Core.ConsumerIndexedSemanticDebtExact as Debt
import DASHI.Core.SetValuedEvidenceConflictExact as Evidence

------------------------------------------------------------------------
-- 1. A camera failure does not globally invalidate a claim when an independent
--    sufficient acoustic route survives.
------------------------------------------------------------------------

data Assumption : Set where
  cameraHealthy audioHealthy : Assumption

Holds : Assumption → Set
Holds cameraHealthy = ⊤
Holds audioHealthy = ⊤

data Route : Set where
  visualRoute acousticRoute : Route

Requires : Route → Assumption → Set
Requires visualRoute cameraHealthy = ⊤
Requires visualRoute audioHealthy = ⊥
Requires acousticRoute cameraHealthy = ⊥
Requires acousticRoute audioHealthy = ⊤

supportFamily : Support.SufficientSupportFamily Assumption Holds ⊤
supportFamily =
  Support.sufficientSupportFamily Route Requires sufficient
  where
    sufficient :
      (route : Route) →
      ((assumption : Assumption) → Requires route assumption → Holds assumption) →
      ⊤
    sufficient route assumptions = tt

BrokenByCameraFailure : Assumption → Set
BrokenByCameraFailure cameraHealthy = ⊤
BrokenByCameraFailure audioHealthy = ⊥

acousticRouteSurvives :
  Support.SurvivingSufficientRoute supportFamily BrokenByCameraFailure
acousticRouteSurvives =
  Support.survivingSufficientRoute acousticRoute proof
  where
    proof :
      (assumption : Assumption) →
      Requires acousticRoute assumption →
      BrokenByCameraFailure assumption →
      ⊥
    proof cameraHealthy required broken = required
    proof audioHealthy required broken = broken

cameraFailureCannotHitEverySufficientRoute :
  Support.AllSufficientRoutesHit supportFamily BrokenByCameraFailure → ⊥
cameraFailureCannotHitEverySufficientRoute =
  Support.survivingSufficientRouteRefutesGlobalInvalidation
    acousticRouteSurvives

------------------------------------------------------------------------
-- 2. Pose and gaze may be different modalities downstream while sharing one
--    upstream video frame; closure-based independence correctly rejects them.
------------------------------------------------------------------------

data Artifact : Set where
  rawFrame poseEvidence gazeEvidence : Artifact

data DependsTiny : Artifact → Artifact → Set where
  frameToPose : DependsTiny rawFrame poseEvidence
  frameToGaze : DependsTiny rawFrame gazeEvidence

RootTiny : Artifact → Set
RootTiny rawFrame = ⊤
RootTiny poseEvidence = ⊥
RootTiny gazeEvidence = ⊥

provenanceSystem : Provenance.ProvenanceSystem Artifact
provenanceSystem = Provenance.provenanceSystem DependsTiny RootTiny

rawFrameReachesPose :
  Provenance.UpstreamOf provenanceSystem rawFrame poseEvidence
rawFrameReachesPose = Closure.affectedStep frameToPose Closure.affectedRefl

rawFrameReachesGaze :
  Provenance.UpstreamOf provenanceSystem rawFrame gazeEvidence
rawFrameReachesGaze = Closure.affectedStep frameToGaze Closure.affectedRefl

sharedVideoRoot :
  Provenance.SharedUpstreamRoot provenanceSystem poseEvidence gazeEvidence
sharedVideoRoot =
  Provenance.sharedUpstreamRoot
    rawFrame tt rawFrameReachesPose rawFrameReachesGaze

poseAndGazeAreNotIndependentByLineage :
  Provenance.IndependentByUpstreamClosure
    provenanceSystem poseEvidence gazeEvidence →
  ⊥
poseAndGazeAreNotIndependentByLineage =
  Provenance.sharedUpstreamRootRefutesIndependence sharedVideoRoot

------------------------------------------------------------------------
-- 3. Passive equality is broken by one admissible communication experiment.
------------------------------------------------------------------------

data State : Set where
  leftState rightState leftAfter rightAfter : State

data Action : Set where
  probe : Action

data Observation : Set where
  sameNow leftResponse rightResponse : Observation

observe : State → Observation
observe leftState = sameNow
observe rightState = sameNow
observe leftAfter = leftResponse
observe rightAfter = rightResponse

step : Action → State → State
step probe leftState = leftAfter
step probe rightState = rightAfter
step probe leftAfter = leftAfter
step probe rightAfter = rightAfter

Admissible : List Action → Set
Admissible (probe ∷ []) = ⊤
Admissible _ = ⊥

language : Experiment.ExperimentLanguage Action
language = Experiment.experimentLanguage Admissible

probeSeparates : leftResponse ≡ rightResponse → ⊥
probeSeparates ()

probeExperiment :
  Experiment.AdmissibleSeparatingExperiment
    language observe step leftState rightState
probeExperiment =
  Experiment.admissibleSeparatingExperiment
    (probe ∷ []) tt probeSeparates

passiveLookalikesNotLanguageEquivalent :
  Experiment.LanguageEquivalent language observe step leftState rightState → ⊥
passiveLookalikesNotLanguageEquivalent =
  Experiment.admissibleSeparatingExperimentRefutesLanguageEquivalence
    probeExperiment

------------------------------------------------------------------------
-- 4. Request/play ambiguity matters to the response consumer and is not
--    covered by the declared margin, so any policy claiming it is deferred is
--    contradictory.
------------------------------------------------------------------------

data Residual : Set where
  requestPlayAmbiguity : Residual

data Consumer : Set where
  chooseHumanResponse : Consumer

Matters : Residual → Consumer → Set
Matters requestPlayAmbiguity chooseHumanResponse = ⊤

MarginCovers : Residual → Consumer → Set
MarginCovers requestPlayAmbiguity chooseHumanResponse = ⊥

semanticDebt : Debt.StructuredConsumerDebt Residual Consumer
semanticDebt = Debt.structuredConsumerDebt Matters MarginCovers

Deferred : Residual → Set
Deferred requestPlayAmbiguity = ⊥

deferralPolicy : Debt.DeferralPolicy semanticDebt
deferralPolicy = Debt.deferralPolicy Deferred proof
  where
    proof :
      ∀ residual consumer →
      Deferred residual →
      Matters residual consumer →
      MarginCovers residual consumer
    proof requestPlayAmbiguity chooseHumanResponse deferred matters = deferred

requestPlayNeedsResolution :
  Debt.NeedsResolution semanticDebt requestPlayAmbiguity chooseHumanResponse
requestPlayNeedsResolution = tt , (λ margin → margin)

requestPlayCannotBeDeferred :
  Deferred requestPlayAmbiguity → ⊥
requestPlayCannotBeDeferred =
  Debt.needsResolutionRefutesDeferral requestPlayNeedsResolution

------------------------------------------------------------------------
-- 5. Exact finite set-valued ambiguity witness is exposed in regression.
------------------------------------------------------------------------

requestOrPlayFamilySupportsRequest :
  Evidence.DemoContains Evidence.requestOrPlay Evidence.request
requestOrPlayFamilySupportsRequest = Evidence.requestOrPlaySupportsRequest

requestOrPlayFamilySupportsPlay :
  Evidence.DemoContains Evidence.requestOrPlay Evidence.play
requestOrPlayFamilySupportsPlay = Evidence.requestOrPlaySupportsPlay
