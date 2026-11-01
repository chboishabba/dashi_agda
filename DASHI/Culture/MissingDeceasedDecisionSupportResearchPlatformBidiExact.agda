module DASHI.Culture.MissingDeceasedDecisionSupportResearchPlatformBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.ApplicationTransformationCapabilityBidiExact as T
import DASHI.Core.RealObjectApplicationBidiExact as R

decisionSource : Source.AttributedSource
decisionSource = Source.mkNoDOISource
  "DASHI / retained Feng Yanghe primary-source lineage"
  "Robust classification and decision-support research object"
  "NUDT/Feng source surfaces retained in-repo"
  "current formalisation"
  "DASHI Feng source owners"
  (Source.namedSourceKind "formalisation composite")
  "Pays a real robust-classification/decision-support research object class; not War Skull same-object identity unless separately sourced."
  Source.publicAttribution

decisionAtlas : Source.AttributedSourceAtlas
decisionAtlas = Source.mkSourceAtlas
  "decision-support research object atlas"
  "DASHI.Culture.MissingDeceasedDecisionSupportResearchPlatformBidiExact"
  (decisionSource ∷ [])
  "Method fit is kept separate from deployment, operational authority and historical programme identity."

classificationRequirement : R.RealObjectRequirement
classificationRequirement = R.mkRequirement
  "robust classification under noisy/redundant attributes"
  "classify observations while explicitly modelling uncertainty, label noise and redundant attributes"
  "Feng Bayesian/noisy-label science owners"
  (T.acquireValidationCorpus ∷ T.acquireUncertaintyModel ∷ T.acquireIntegrationWorkflow ∷ [])
  "Executable deployment requires exact equations, priors, sampling rule, dataset, decision loss and held-out evaluation."

decisionSupportResearchPlatformObject : R.RealEngineeringObject
decisionSupportResearchPlatformObject = R.real-engineering-object
  "robust classification / decision-support research platform"
  "benign statistical-methods research object"
  decisionAtlas
  (classificationRequirement ∷ [])
  "evaluate Bayesian/noisy-label classification methods under controlled datasets and nulls"
  "A generic decision-support object does not establish that War Skull or any military system used the exact method."

fengFit : R.ScientistObjectFit
fengFit = R.mkFit
  "Feng Yanghe"
  "DASHI Feng Bayesian/noisy-label owners"
  "multi-group-graph Bayesian classification and noisy-label method family"
  classificationRequirement R.directSourceFit
  "retained Feng publisher/NUDT science lineage"
  "Direct method fit to the robust-classification research subsystem."
  "recover exact equations, priors, example datasets, sampling rule and metrics; separately prove any War Skull same-object link"
  false
  "Method authorship does not establish deployment in War Skull, shared programme identity or event cause."

fengDirectFit : Bool
fengDirectFit = true

historicalParticipationPaid : Bool
historicalParticipationPaid = false
