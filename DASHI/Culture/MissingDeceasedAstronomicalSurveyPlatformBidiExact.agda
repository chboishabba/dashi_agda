module DASHI.Culture.MissingDeceasedAstronomicalSurveyPlatformBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.ApplicationTransformationCapabilityBidiExact as T
import DASHI.Core.RealObjectApplicationBidiExact as R

astronomySource : Source.AttributedSource
astronomySource = Source.mkNoDOISource
  "DASHI / retained Grillmair primary-source lineage"
  "Wide-field stellar-stream survey and orbit-inference object"
  "Grillmair/IPAC/Caltech source surfaces already retained in-repo"
  "current formalisation"
  "DASHI Grillmair source owners"
  (Source.namedSourceKind "formalisation composite")
  "Pays only the existence of a real astronomical-survey/inference object class; not a shared historical programme for the retained cohort."
  Source.publicAttribution

astronomyAtlas : Source.AttributedSourceAtlas
astronomyAtlas = Source.mkSourceAtlas
  "astronomical-survey object atlas"
  "DASHI.Culture.MissingDeceasedAstronomicalSurveyPlatformBidiExact"
  (astronomySource ∷ [])
  "Source composition imports neither proof nor historical participation."

surveyRequirement : R.RealObjectRequirement
surveyRequirement = R.mkRequirement
  "wide-field astronomical survey and stream inference"
  "acquire calibrated sky observations, construct matched-filter/catalogue products and infer stellar-stream/orbit structure"
  "Grillmair stellar-stream science owners"
  (T.acquireValidationCorpus ∷ T.acquireUncertaintyModel ∷ T.acquireIntegrationWorkflow ∷ [])
  "Survey inference requires explicit catalogue version, photometric calibration, selection function and orbit-model assumptions."

astronomicalSurveyObject : R.RealEngineeringObject
astronomicalSurveyObject = R.real-engineering-object
  "wide-field astronomical survey / stellar-stream inference platform"
  "benign astronomy research object"
  astronomyAtlas
  (surveyRequirement ∷ [])
  "detect and characterise stellar streams and use them for Galactic-structure/orbit inference"
  "Object fit does not establish historical participation in any particular survey beyond separately sourced receipts."

grillmairFit : R.ScientistObjectFit
grillmairFit = R.mkFit
  "Carl J. Grillmair"
  "DASHI Grillmair stellar-stream owners"
  "matched-filter stellar-stream detection and orbit inference"
  surveyRequirement R.directSourceFit
  "retained Grillmair/IPAC primary science lineage"
  "Direct science fit to the survey-analysis subsystem."
  "recover exact catalogue/filter/orbit inputs, uncertainty model and post-loss data/code custody"
  false
  "Science fit does not create a cross-person programme or event cause."

grillmairDirectFit : Bool
grillmairDirectFit = true

historicalParticipationPaid : Bool
historicalParticipationPaid = false
