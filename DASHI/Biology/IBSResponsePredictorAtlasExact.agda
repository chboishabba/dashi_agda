module DASHI.Biology.IBSResponsePredictorAtlasExact where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.IBSCausalMaintenanceRegimeExact as Regime
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Snowball

------------------------------------------------------------------------
-- RESPONSE PREDICTION IS NOT CAUSAL IDENTIFICATION
------------------------------------------------------------------------

lee2026Source : Source.AttributedSource
lee2026Source = Source.mkDOISource
  "Allen A Lee et al."
  "A Randomized Trial of Rifaximin vs Low FODMAP Diet for Symptom Outcomes and Microbiome Changes in Irritable Bowel Syndrome"
  "Clinical Gastroenterology and Hepatology" "2026"
  "10.1016/j.cgh.2026.04.014"
  "https://doi.org/10.1016/j.cgh.2026.04.014"
  Source.academicArticleSource
  "Randomized comparative IBS-D trial. Distinct baseline taxa associated with response to low-FODMAP versus rifaximin, while both interventions improved overlapping clinical endpoints. Baseline taxa are response predictors, not validated mediators or maintenance-regime labels."
  Source.publicAttribution

jacobs2021Source : Source.AttributedSource
jacobs2021Source = Source.mkDOISource
  "Jonathan P Jacobs; Arpana Gupta; Ravi R Bhatt et al."
  "Cognitive behavioral therapy for irritable bowel syndrome induces bidirectional alterations in the brain-gut-microbiome axis associated with gastrointestinal symptom improvement"
  "Microbiome 9:236" "2021"
  "10.1186/s40168-021-01188-6"
  "https://doi.org/10.1186/s40168-021-01188-6"
  Source.academicArticleSource
  "CBT cohort nested in a randomized trial: baseline microbiome/serotonin and brain features associated with response; an 11-genus random-forest classifier reported high internal discrimination. Co-correlated brain/microbiome changes and internal prediction do not establish causal mediation or externally validated treatment selection."
  Source.publicAttribution

manning2026Source : Source.AttributedSource
manning2026Source = Source.mkDOISource
  "Lauren P Manning; Maaike Van Den Houte; Caroline J Tuck et al."
  "Psychological Factors Predict Response to a Low FODMAP Dietary Intervention in Irritable Bowel Syndrome: A Prospective Cohort Study"
  "United European Gastroenterology Journal 14(3):e70204" "2026"
  "10.1002/ueg2.70204"
  "https://doi.org/10.1002/ueg2.70204"
  Source.academicArticleSource
  "Prospective low-FODMAP cohort: gastrointestinal-specific anxiety, distress, illness perceptions, treatment credibility/expectancy and personal control were associated with subsequent outcome trajectories. These predictors are not unique biological mechanisms and expectancy effects do not invalidate biological fibres."
  Source.publicAttribution

andafa2026Source : Source.AttributedSource
andafa2026Source = Source.mkDOISource
  "Temebi W Andafa; Emmanuel C Imoh; Sheriffdeen A Adekanmbi"
  "Artificial Intelligence Applied to the Brain-Gut Axis in Irritable Bowel Syndrome: Advancing Toward Clinical Translation"
  "Cureus 18(5):e109142" "2026"
  "10.7759/cureus.109142"
  "https://doi.org/10.7759/cureus.109142"
  Source.academicArticleSource
  "Narrative review of AI/ML across microbiome, neuroimaging, multi-omics and psychological data. Treatment-response prediction evidence remains exploratory, often small/single-centre/internal-validation, with overfitting and leakage risks. Review-level synthesis does not validate a clinical model."
  Source.publicAttribution

data PredictorDomain : Set where
  microbiomeCompositionPredictor : PredictorDomain
  microbialFunctionPredictor : PredictorDomain
  metabolitePredictor : PredictorDomain
  brainConnectivityPredictor : PredictorDomain
  autonomicPredictor : PredictorDomain
  psychologicalPredictor : PredictorDomain
  multimodalPredictor : PredictorDomain

data PredictorEvidenceStatus : Set where
  randomizedTrialAssociatedPredictor : PredictorEvidenceStatus
  prospectiveCohortPredictor : PredictorEvidenceStatus
  internallyValidatedModel : PredictorEvidenceStatus
  reviewLevelCandidate : PredictorEvidenceStatus
  externallyValidatedModel : PredictorEvidenceStatus

record TreatmentResponsePredictor : Set where
  constructor treatment-response-predictor
  field
    source : Source.AttributedSource
    treatmentReference : String
    predictorDomains : List PredictorDomain
    evidenceStatus : PredictorEvidenceStatus
    predictedOutcome : String
    validationReference : String
    mediationEstablished : Bool
    externalTransportEstablished : Bool
    participantMechanismIdentified : Bool
open TreatmentResponsePredictor public

lowFODMAPRifaximinPredictor : TreatmentResponsePredictor
lowFODMAPRifaximinPredictor = treatment-response-predictor
  lee2026Source
  "5-week low-FODMAP versus rifaximin randomized comparison in IBS-D"
  (microbiomeCompositionPredictor ∷ [])
  randomizedTrialAssociatedPredictor
  "treatment-specific pain/bloating response"
  "distinct baseline taxa associated with response; breath testing inconsistent"
  false false false

cbtBrainGutPredictor : TreatmentResponsePredictor
cbtBrainGutPredictor = treatment-response-predictor
  jacobs2021Source
  "cognitive behavioural therapy in IBSOS-derived cohort"
  (microbiomeCompositionPredictor ∷ metabolitePredictor ∷ brainConnectivityPredictor ∷ multimodalPredictor ∷ [])
  internallyValidatedModel
  "CBT response"
  "internal multivariate/random-forest analyses; reported 11-genus AUROC 0.96, no external validation imported"
  false false false

lowFODMAPPsychologicalPredictor : TreatmentResponsePredictor
lowFODMAPPsychologicalPredictor = treatment-response-predictor
  manning2026Source
  "three-phase low-FODMAP intervention over six months"
  (psychologicalPredictor ∷ [])
  prospectiveCohortPredictor
  "symptom and quality-of-life trajectory"
  "prospective repeated questionnaires / cross-lagged analyses"
  false false false

aiTranslationReviewPredictor : TreatmentResponsePredictor
aiTranslationReviewPredictor = treatment-response-predictor
  andafa2026Source
  "cross-study IBS brain-gut AI/ML literature"
  (multimodalPredictor ∷ [])
  reviewLevelCandidate
  "classification and treatment-response outcomes"
  "narrative review emphasizes small cohorts, internal validation, overfitting/data-leakage and external-replication gaps"
  false false false

canonicalIBSResponsePredictorAtlas : List TreatmentResponsePredictor
canonicalIBSResponsePredictorAtlas =
  lowFODMAPRifaximinPredictor ∷ cbtBrainGutPredictor ∷
  lowFODMAPPsychologicalPredictor ∷ aiTranslationReviewPredictor ∷ []

data PredictorIsMediatorPermission : Set where
predictorDoesNotBecomeMediator : PredictorIsMediatorPermission → ⊥
predictorDoesNotBecomeMediator ()

data InternalPredictionIsValidatedClinicalClassifierPermission : Set where
internalPredictionDoesNotBecomeClinicalClassifier :
  InternalPredictionIsValidatedClinicalClassifierPermission → ⊥
internalPredictionDoesNotBecomeClinicalClassifier ()

data PredictorIdentifiesMaintenanceRegimePermission : Set where
predictorDoesNotIdentifyMaintenanceRegime : PredictorIdentifiesMaintenanceRegimePermission → ⊥
predictorDoesNotIdentifyMaintenanceRegime ()

data ResponseAssociationTransportsAcrossTreatmentPermission : Set where
responseAssociationDoesNotTransportAcrossTreatment : ResponseAssociationTransportsAcrossTreatmentPermission → ⊥
responseAssociationDoesNotTransportAcrossTreatment ()

record ResponsePredictionWeld : Set where
  constructor response-prediction-weld
  field
    causalRegimeBoundary : Regime.IBSCausalMaintenanceBoundary
    treatmentSpecificityRetained : Bool
    predictorMediatorSeparationRetained : Bool
    internalExternalValidationSeparated : Bool
    participantMechanismNotInferredFromPrediction : Bool
open ResponsePredictionWeld public

canonicalResponsePredictionWeld : ResponsePredictionWeld
canonicalResponsePredictionWeld = response-prediction-weld
  Regime.canonicalIBSCausalMaintenanceBoundary true true true true

data PredictorAcquisitionStatus : Set where
  acquiredTreatmentSpecificSignal : PredictorAcquisitionStatus
  externalReplicationNeeded : PredictorAcquisitionStatus
  calibrationNeeded : PredictorAcquisitionStatus
  prospectiveUtilityTrialNeeded : PredictorAcquisitionStatus
  causalMediationNeeded : PredictorAcquisitionStatus

record ResponsePredictionParetoNode : Set where
  constructor response-prediction-pareto-node
  field
    label : String
    status : PredictorAcquisitionStatus
    route : Snowball.DiscoveryRoute
    paidReference : String
    residual : String
    nextAcquisition : String
    attributionBoundary : String
open ResponsePredictionParetoNode public

microbialTreatmentInteractionNode : ResponsePredictionParetoNode
microbialTreatmentInteractionNode = response-prediction-pareto-node
  "treatment-specific microbial response prediction"
  acquiredTreatmentSpecificSignal Snowball.externalKnowledgeComparison
  "Lee 2026 DOI 10.1016/j.cgh.2026.04.014"
  "taxa associations may be cohort-, diet-, pipeline- or treatment-specific"
  "external replication with harmonized endpoints plus metatranscriptome/metabolome and exposure adherence"
  "associated taxa are neither mediator nor regime classifier"

cbtMultimodalNode : ResponsePredictionParetoNode
cbtMultimodalNode = response-prediction-pareto-node
  "brain-gut-microbiome CBT response model"
  externalReplicationNeeded Snowball.externalKnowledgeComparison
  "Jacobs 2021 DOI 10.1186/s40168-021-01188-6"
  "small microbiome subset and internal model validation"
  "locked-model held-out multi-site replication with preregistered calibration and decision threshold"
  "reported AUROC is internal prediction evidence, not clinical utility"

psychologicalDietNode : ResponsePredictionParetoNode
psychologicalDietNode = response-prediction-pareto-node
  "psychological modifiers of dietary response"
  acquiredTreatmentSpecificSignal Snowball.externalKnowledgeComparison
  "Manning 2026 DOI 10.1002/ueg2.70204"
  "psychological predictors can be modifiers, mediators, adherence determinants or correlated state"
  "joint model with exposure/adherence, biological fibres and treatment interaction"
  "association does not establish a purely psychological mechanism"

clinicalUtilityNode : ResponsePredictionParetoNode
clinicalUtilityNode = response-prediction-pareto-node
  "prospective predictor-guided treatment selection"
  prospectiveUtilityTrialNeeded Snowball.experimentalDesign
  "current treatment predictors are mostly retrospective/exploratory or internally validated"
  "unknown whether using the predictor improves outcomes relative to standard selection"
  "randomize predictor-guided versus standard treatment allocation with locked model and patient-centred outcomes"
  "prediction accuracy alone is not clinical utility"

mediationNode : ResponsePredictionParetoNode
mediationNode = response-prediction-pareto-node
  "predictor-to-mediator promotion"
  causalMediationNeeded Snowball.experimentalDesign
  "IBSCausalMaintenanceRegimeExact reuses CausalEffectEstimandExact"
  "predictive feature may not lie on causal treatment path"
  "predeclare mediator and use intervention/comparator/time-specific mediation estimand"
  "feature importance or association is not mediation"

canonicalIBSResponsePredictionParetoFrontier : List ResponsePredictionParetoNode
canonicalIBSResponsePredictionParetoFrontier =
  microbialTreatmentInteractionNode ∷ cbtMultimodalNode ∷ psychologicalDietNode ∷
  clinicalUtilityNode ∷ mediationNode ∷ []

record IBSResponsePredictorBoundary : Set where
  constructor ibs-response-predictor-boundary
  field
    predictorMayAidTreatmentSelectionResearch : Bool
    predictorEqualsMediator : Bool
    internalValidationEqualsExternalValidation : Bool
    predictorEqualsParticipantMechanism : Bool
    predictorAccuracyEqualsClinicalUtility : Bool
    treatmentSpecificityRetained : Bool

canonicalIBSResponsePredictorBoundary : IBSResponsePredictorBoundary
canonicalIBSResponsePredictorBoundary = ibs-response-predictor-boundary
  true false false false false true
