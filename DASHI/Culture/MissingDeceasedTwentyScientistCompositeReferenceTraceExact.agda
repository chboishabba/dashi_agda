module DASHI.Culture.MissingDeceasedTwentyScientistCompositeReferenceTraceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistEmbodiedTechnologyBidiExact as E
import DASHI.Culture.MissingDeceasedTwentyScientistEmbodiedReferenceRuntimeBidiExact as R
import DASHI.Culture.MissingDeceasedTwentyScientistCompositeApplicationProofDebtExact as D

------------------------------------------------------------------------
-- ROUND-10 COMPOSITE REFERENCE TRACES
--
-- The two currently ungated composite applications are compiled into ordered
-- reference traces.  Ranking is for proof/acquisition efficiency only.  It does
-- not upgrade source strength, pay engineering qualification, or establish any
-- historical integrated system.
------------------------------------------------------------------------

data TracePriority : Set where
  replayFirst qualificationFirst validationFirst operatingWindowFirst custodyLater : TracePriority

record RankedSoftResidual : Set where
  constructor ranked-soft-residual
  field
    rank : Nat
    owner : String
    priority : TracePriority
    missingCoordinate : String
    whyNow : String

open RankedSoftResidual public

record CompositeReferenceTrace : Set where
  constructor composite-reference-trace
  field
    application : E.CompositeApplication
    runtimePlan : R.ReferenceApplicationPlan
    proofDebt : D.CompositeApplicationProofDebt
    rankedSoftResiduals : List RankedSoftResidual
    hardGateFree : Bool
    traceIntent : String
    boundedReading : String

open CompositeReferenceTrace public

longDurationResiduals : List RankedSoftResidual
longDurationResiduals =
  ranked-soft-residual 1 "Frank W. Maiwald" replayFirst
    "raw action-spectrum intensity/calibration data"
    "converts an existing source-coordinate replay into a quantitative diagnostic replay" ∷
  ranked-soft-residual 2 "Zhou Guangyuan" replayFirst
    "multi-sample aerogel synthesis/property table"
    "turns one SI datum into a process/property surface used directly by thermal protection" ∷
  ranked-soft-residual 3 "Joshua Kyle LeBlanc" qualificationFirst
    "named device qualification, calibration and failure evidence"
    "harsh-environment control is application-critical and presently not device-qualified" ∷
  ranked-soft-residual 4 "Monica Jacinto / Monica Reza" operatingWindowFirst
    "MONDALOY/enamel descendant operating and qualification window"
    "material compatibility requires a source-exact oxygen-service process window" ∷
  ranked-soft-residual 5 "Zhang Daibing" validationFirst
    "one source-exact autonomy/control replay"
    "autonomous mobility needs a real dynamics/control/test witness rather than only a mechanism shape" ∷
  ranked-soft-residual 6 "Nuno F. G. Loureiro" custodyLater
    "Viriato repository/simulation-state handover"
    "important for person-specific continuity but not required to execute the public science mechanism" ∷ []

longDurationCompositeTrace : CompositeReferenceTrace
longDurationCompositeTrace = composite-reference-trace
  E.longDurationSciencePlatform
  R.longDurationReferencePlan
  D.longDurationProofDebt
  longDurationResiduals
  true
  "execute the public/finite science interfaces while routing the highest-value replay and qualification residuals"
  "A reference trace is an application/proof-debt schedule. It does not establish operational qualification, historical deployment, roster collaboration, possession, or event cause."

autonomousSurveyResiduals : List RankedSoftResidual
autonomousSurveyResiduals =
  ranked-soft-residual 1 "Zhang Xiaoxin" replayFirst
    "forecast whitening/CEEMDAN/CWT hyperparameters, code and data"
    "existing source replay already exposes event counts and accuracy, so parameters/code give the largest executable gain" ∷
  ranked-soft-residual 2 "Carl J. Grillmair" replayFirst
    "source survey slice, matched-filter weights and orbit uncertainty"
    "the matched-filter machinery already exists; a source data slice turns it into a genuine replay" ∷
  ranked-soft-residual 3 "Michael David Hicks" replayFirst
    "source lightcurve, viewing geometry and calibration"
    "replaces a synthetic photometry carrier with an observation-bound inference" ∷
  ranked-soft-residual 4 "Feng Yanghe" replayFirst
    "source classifier equations, data and label-noise parameters"
    "separates published statistical science from the still-unpaid War Skull implementation seam" ∷
  ranked-soft-residual 5 "Chen Shuming" validationFirst
    "source hardware-verification graph, stimuli, coverage and mismatch example"
    "turns graph-verification topology into an auditable processor-assurance example" ∷
  ranked-soft-residual 6 "Zhang Daibing" validationFirst
    "source dynamics, gains, sensor model, geometry and error series"
    "pays one concrete autonomy/control validation surface" ∷
  ranked-soft-residual 7 "Liu Donghao" qualificationFirst
    "authored DSMM maturity levels, scoring semantics and assessed example"
    "replaces a synthetic governance score shape with an attributable operational rubric" ∷ []

autonomousSurveyCompositeTrace : CompositeReferenceTrace
autonomousSurveyCompositeTrace = composite-reference-trace
  E.autonomousRemoteSurveyPlatform
  R.autonomousSurveyReferencePlan
  D.autonomousSurveyProofDebt
  autonomousSurveyResiduals
  true
  "execute survey/autonomy/inference fibres while replacing the most informative synthetic carriers with source replays"
  "No hard roster gate is present, but source replay, validation and qualification debt remain. Trace order is not evidence of historical integration."

ungatedCompositeTraces : List CompositeReferenceTrace
ungatedCompositeTraces = longDurationCompositeTrace ∷ autonomousSurveyCompositeTrace ∷ []

ungatedCompositeTraceCount : Nat
ungatedCompositeTraceCount = 2

traceRanksSoftResiduals : Bool
traceRanksSoftResiduals = true

traceExecutionDoesNotPayQualification : Bool
traceExecutionDoesNotPayQualification = false

traceExecutionDoesNotPayHistoricalDeployment : Bool
traceExecutionDoesNotPayHistoricalDeployment = false

traceExecutionDoesNotPaySourceReplication : Bool
traceExecutionDoesNotPaySourceReplication = false

traceExecutionDoesNotPayRosterCollaboration : Bool
traceExecutionDoesNotPayRosterCollaboration = false

traceCanRefineAcquisitionPareto : Bool
traceCanRefineAcquisitionPareto = true
