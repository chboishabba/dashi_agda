module DASHI.Biology.IBSCausalMaintenanceRegimeExact where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.IBSGutBrainImmuneSystemsHyperfabricExact as Whole
import DASHI.Biology.IBSSystemsIdentificationParetoExact as Systems
import DASHI.Biology.IBSLatentStateTransitionExact as Transition
import DASHI.Biology.IBSMechanismProbePerturbationAtlasExact as Probe
import DASHI.Biology.CausalEffectEstimandExact as Causal
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Snowball

------------------------------------------------------------------------
-- IBS CAUSAL MAINTENANCE REGIME HYPOTHESES
--
-- Sources pay only the observations/designs explicitly attributed below.
-- Candidate regimes are repo-side structural hypotheses, not source claims.
------------------------------------------------------------------------

black2026Source : Source.AttributedSource
black2026Source = Source.mkDOISource
  "Christopher J Black et al."
  "Pathophysiology of irritable bowel syndrome"
  "The Lancet Gastroenterology & Hepatology" "2026"
  "10.1016/S2468-1253(26)00148-2"
  "https://doi.org/10.1016/S2468-1253(26)00148-2"
  Source.academicArticleSource
  "Review-level support for integrated peripheral and central IBS mechanisms including microbiome, permeability, immune function, motility, visceral hypersensitivity, bile acids, carbohydrate metabolism and central pain processing. It does not identify a participant-specific maintenance regime."
  Source.publicAttribution

actionable2025Source : Source.AttributedSource
actionable2025Source = Source.mkDOISource
  "Andrea Shin; Kyle Staller; David J Levinthal"
  "Actionable Clinical Features and Biomarkers to Facilitate the Management of Irritable Bowel Syndrome"
  "American Journal of Gastroenterology" "2025"
  "10.14309/ajg.0000000000003859"
  "https://doi.org/10.14309/ajg.0000000000003859"
  Source.academicArticleSource
  "Review-level argument for mechanism-informed clinical features and biomarkers because symptom subtype does not identify the active mechanism in an individual. It does not validate a causal classifier. David J Levinthal is retained as this paper's author and is not identified with Michael Levin or the repo's Levin bioelectric programme."
  Source.publicAttribution

jarrett2015Source : Source.AttributedSource
jarrett2015Source = Source.mkDOISource
  "Monica E Jarrett et al."
  "Balance of Autonomic Nervous System Predicts Who Benefits from a Self-management Intervention Program for Irritable Bowel Syndrome"
  "Journal of Neurogastroenterology and Motility 21(4):572-580" "2015"
  "10.5056/jnm15067"
  "https://doi.org/10.5056/jnm15067"
  Source.academicArticleSource
  "Randomized self-management trial secondary biomarker analysis: baseline autonomic measures predicted differential abdominal-pain benefit while cortisol, IL-10 and lactulose/mannitol did not significantly predict benefit. Prediction of response does not identify a unique causal regime."
  Source.publicAttribution

wish2026Source : Source.AttributedSource
wish2026Source = Source.mkDOISource
  "Elizabeth N Madva et al."
  "The WISH 2.0 Intervention for Irritable Bowel Syndrome: Protocol for a Pilot Randomized Controlled Trial"
  "JMIR Research Protocols 15:e98352" "2026"
  "10.2196/98352"
  "https://doi.org/10.2196/98352"
  Source.academicArticleSource
  "Protocol-level evidence only: plans repeated candidate gut-brain mechanism measurements including HRV, interoception, whole-transcriptome RNA sequencing and serum inflammatory biomarkers around a behavioural intervention. No completed causal result is imported."
  Source.publicAttribution

nitns2026Source : Source.AttributedSource
nitns2026Source = Source.mkDOISource
  "Yanbin Wei; Zihe Shi; Shanshan Wu; Xin Yao"
  "Efficacy and safety of non-invasive transcutaneous nerve stimulation in patients with irritable bowel syndrome: a systematic review and meta-analysis"
  "Therapeutic Advances in Gastroenterology 19:17562848261436121" "2026"
  "10.1177/17562848261436121"
  "https://doi.org/10.1177/17562848261436121"
  Source.academicArticleSource
  "Four RCTs / 170 participants were synthesized; symptom and quality-of-life outcomes improved and HRV findings suggested possible autonomic modulation, but evidence quality was low to very low and does not establish an autonomic-only IBS mechanism."
  Source.publicAttribution

data MaintenanceRegimeCandidate : Set where
  microbialImmuneCandidate : MaintenanceRegimeCandidate
  barrierSensoryCandidate : MaintenanceRegimeCandidate
  autonomicCentralGainCandidate : MaintenanceRegimeCandidate
  bileAcidMotilityCandidate : MaintenanceRegimeCandidate
  mixedCoupledCandidate : MaintenanceRegimeCandidate

data RegimeAuthority : Set where
  structuralHypothesisOnly : RegimeAuthority
  stratificationSupported : RegimeAuthority
  interventionPredictiveAssociation : RegimeAuthority
  causalRegimeValidated : RegimeAuthority

record CandidateMaintenanceRegime : Set where
  constructor candidate-maintenance-regime
  field
    label : MaintenanceRegimeCandidate
    dominantFibres : List Whole.IBSSystemFibre
    supportingReference : String
    discriminatingObservation : String
    discriminatingPerturbation : String
    currentAuthority : RegimeAuthority
    participantClassifierValidated : Bool
    causalClosureClaimed : Bool
open CandidateMaintenanceRegime public

microbialImmuneRegime : CandidateMaintenanceRegime
microbialImmuneRegime = candidate-maintenance-regime
  microbialImmuneCandidate
  (Whole.microbiomeMetaboliteFibre ∷ Whole.mucosalImmuneMastCellFibre ∷ Whole.epithelialBarrierFibre ∷ [])
  "Black 2026 integrated pathophysiology review; existing De Palma/Gao histamine/LPS-mast-cell lanes; Mars 2020 longitudinal multi-omics"
  "repeated microbial function + metabolome + mast-cell/immune + barrier measurements around flare/recovery"
  "microbiome-directed or diet/substrate perturbation with matched non-microbial fibres measured"
  structuralHypothesisOnly false false

barrierSensoryRegime : CandidateMaintenanceRegime
barrierSensoryRegime = candidate-maintenance-regime
  barrierSensoryCandidate
  (Whole.epithelialBarrierFibre ∷ Whole.visceralSensoryNociceptiveFibre ∷ Whole.mucosalImmuneMastCellFibre ∷ [])
  "Black 2026 review plus existing Gao barrier/mast-cell and H1/TRPV1 evidence lanes"
  "barrier/permeability + visceral sensitivity + mast-cell/histamine trajectories"
  "barrier- or sensory-targeted perturbation with proximal target engagement and distal symptom trajectory"
  structuralHypothesisOnly false false

autonomicCentralRegime : CandidateMaintenanceRegime
autonomicCentralRegime = candidate-maintenance-regime
  autonomicCentralGainCandidate
  (Whole.autonomicHPAAllostaticFibre ∷ Whole.centralPainInteroceptiveFibre ∷ Whole.visceralSensoryNociceptiveFibre ∷ [])
  "Bai 2026 ANS review; Jarrett 2015 response-prediction analysis; Lowen 2013 intervention/fMRI surface"
  "dense autonomic + interoceptive/central + symptom trajectories with peripheral fibres retained"
  "brain-gut behavioural or neuromodulatory perturbation with peripheral and central readouts"
  interventionPredictiveAssociation false false

bileAcidMotilityRegime : CandidateMaintenanceRegime
bileAcidMotilityRegime = candidate-maintenance-regime
  bileAcidMotilityCandidate
  (Whole.neurochemicalMetabolicFibre ∷ Whole.entericMotilitySecretionFibre ∷ Whole.microbiomeMetaboliteFibre ∷ [])
  "existing Di Ciaula bile-acid review and colesevelam mechanism-probe lane"
  "C4/FGF19/fecal bile acids + transit + microbiome + symptom trajectory"
  "bile-acid sequestration or other validated bile-acid perturbation with target engagement"
  stratificationSupported false false

mixedCoupledRegime : CandidateMaintenanceRegime
mixedCoupledRegime = candidate-maintenance-regime
  mixedCoupledCandidate
  (Whole.microbiomeMetaboliteFibre ∷ Whole.epithelialBarrierFibre ∷ Whole.mucosalImmuneMastCellFibre ∷
   Whole.autonomicHPAAllostaticFibre ∷ Whole.centralPainInteroceptiveFibre ∷ Whole.visceralSensoryNociceptiveFibre ∷ [])
  "Black 2026 integrated DGBI model and current whole-system hyperfabric"
  "multi-fibre repeated panel with transition and response data"
  "orthogonal sequential perturbations; no one intervention is assumed sufficient"
  structuralHypothesisOnly false false

canonicalCandidateMaintenanceRegimeAtlas : List CandidateMaintenanceRegime
canonicalCandidateMaintenanceRegimeAtlas =
  microbialImmuneRegime ∷ barrierSensoryRegime ∷ autonomicCentralRegime ∷
  bileAcidMotilityRegime ∷ mixedCoupledRegime ∷ []

data SymptomPatternIdentifiesMaintenanceRegimePermission : Set where
symptomPatternDoesNotIdentifyMaintenanceRegime : SymptomPatternIdentifiesMaintenanceRegimePermission → ⊥
symptomPatternDoesNotIdentifyMaintenanceRegime ()

data SingleInterventionResponseIdentifiesUniqueRegimePermission : Set where
singleInterventionResponseDoesNotIdentifyUniqueRegime : SingleInterventionResponseIdentifiesUniqueRegimePermission → ⊥
singleInterventionResponseDoesNotIdentifyUniqueRegime ()

data BiomarkerPanelEqualsCausalRegimePermission : Set where
biomarkerPanelDoesNotEqualCausalRegime : BiomarkerPanelEqualsCausalRegimePermission → ⊥
biomarkerPanelDoesNotEqualCausalRegime ()

data PredictiveBiomarkerIsMediatorPermission : Set where
predictiveBiomarkerDoesNotBecomeMediator : PredictiveBiomarkerIsMediatorPermission → ⊥
predictiveBiomarkerDoesNotBecomeMediator ()

data LevinthalIsMichaelLevinPermission : Set where
levinthalCitationDoesNotBecomeMichaelLevinCitation : LevinthalIsMichaelLevinPermission → ⊥
levinthalCitationDoesNotBecomeMichaelLevinCitation ()

record RegimeDiscriminationPanel : Set where
  constructor regime-discrimination-panel
  field
    symptomTrajectory : Systems.MeasurementAxis
    microbialFunction : Systems.MeasurementAxis
    metabolome : Systems.MeasurementAxis
    immuneMastCell : Systems.MeasurementAxis
    barrier : Systems.MeasurementAxis
    bileAcid : Systems.MeasurementAxis
    autonomic : Systems.MeasurementAxis
    visceralSensitivity : Systems.MeasurementAxis
    centralInteroception : Systems.MeasurementAxis
    exposure : Systems.MeasurementAxis
    repeatedWithinPerson : Bool
    eventTriggeredSampling : Bool
    atLeastTwoOrthogonalPerturbationsPreferred : Bool
    historyLedgerRequired : Bool
    validatedClinicalClassifier : Bool
open RegimeDiscriminationPanel public

canonicalRegimeDiscriminationPanel : RegimeDiscriminationPanel
canonicalRegimeDiscriminationPanel = regime-discrimination-panel
  Systems.symptomTrajectoryAxis Systems.microbiomeFunctionAxis Systems.metabolomeAxis
  Systems.histamineMastCellAxis Systems.epithelialBarrierAxis Systems.bileAcidAxis
  Systems.autonomicAxis Systems.visceralSensitivityAxis Systems.centralInteroceptivePainAxis
  Systems.dietExposureAxis true true true true false

record MaintenanceCausalEstimandObligation : Set₁ where
  constructor maintenance-causal-estimand-obligation
  field
    causalBoundary : Causal.CausalEffectEstimandBoundary
    targetRegime : MaintenanceRegimeCandidate
    interventionReference : String
    comparatorReference : String
    proximalOutcomeReference : String
    distalOutcomeReference : String
    timeHorizonReference : String
    mediatorIfClaimedMustBeExplicit : Bool
    populationAndIndividualEffectsRemainDistinct : Bool
open MaintenanceCausalEstimandObligation public

canonicalMaintenanceCausalEstimandObligation : MaintenanceCausalEstimandObligation
canonicalMaintenanceCausalEstimandObligation = maintenance-causal-estimand-obligation
  Causal.canonicalCausalEffectEstimandBoundary mixedCoupledCandidate
  "mechanism-selective perturbation, predeclared"
  "matched sham/control/alternative fibre perturbation"
  "proximal target-engagement coordinate"
  "symptom/functional trajectory plus competing-fibre responses"
  "predeclared acute + recovery + persistence horizons"
  true true

data RegimeAcquisitionStatus : Set where
  boundedEvidenceAcquired : RegimeAcquisitionStatus
  prospectiveDiscriminationNeeded : RegimeAcquisitionStatus
  orthogonalPerturbationNeeded : RegimeAcquisitionStatus
  mediatorIdentificationNeeded : RegimeAcquisitionStatus
  externalTransportNeeded : RegimeAcquisitionStatus

record CausalMaintenanceParetoNode : Set where
  constructor causal-maintenance-pareto-node
  field
    label : String
    status : RegimeAcquisitionStatus
    route : Snowball.DiscoveryRoute
    sourceOrOwnerReference : String
    residual : String
    acquisition : String
    attributionBoundary : String
open CausalMaintenanceParetoNode public

autonomicPredictionNode : CausalMaintenanceParetoNode
autonomicPredictionNode = causal-maintenance-pareto-node
  "autonomic baseline as differential-response predictor" boundedEvidenceAcquired Snowball.externalKnowledgeComparison
  "Jarrett 2015 DOI 10.5056/jnm15067"
  "prediction may reflect arousal, central state, correlated peripheral state or effect modification"
  "replicate under preregistered treatment-by-autonomic interaction with synchronized gut/immune/central measurements"
  "predictive moderation is not mediation or unique maintenance-regime identification"

brainGutTrialDesignNode : CausalMaintenanceParetoNode
brainGutTrialDesignNode = causal-maintenance-pareto-node
  "multi-fibre brain-gut intervention measurement" prospectiveDiscriminationNeeded Snowball.experimentalDesign
  "WISH 2.0 protocol DOI 10.2196/98352: HRV + interoception + transcriptome + inflammatory biomarkers"
  "protocol has not yet produced efficacy or mediation evidence"
  "preserve treatment/control contrast and model proximal, distal and mediator outcomes separately when results mature"
  "planned measurement is not acquired causal evidence"

neuromodulationNode : CausalMaintenanceParetoNode
neuromodulationNode = causal-maintenance-pareto-node
  "autonomic neuromodulation as system probe" boundedEvidenceAcquired Snowball.externalKnowledgeComparison
  "Wei et al. 2026 DOI 10.1177/17562848261436121; four RCTs / 170 participants"
  "low/very-low quality evidence and heterogeneous modalities/subtypes; HRV mechanism remains suggestive"
  "larger sham-controlled trials with HRV plus peripheral mechanistic panel and trajectory outcomes"
  "clinical benefit does not prove autonomic-only maintenance"

orthogonalProbeNode : CausalMaintenanceParetoNode
orthogonalProbeNode = causal-maintenance-pareto-node
  "orthogonal sequential perturbation discrimination" orthogonalPerturbationNeeded Snowball.experimentalDesign
  "existing IBSMechanismProbePerturbationAtlasExact"
  "one responder contrast cannot separate shared downstream pathways from the intended target fibre"
  "within-person randomized/crossover sequence of at least two fibre-distinct probes with washout and common measurement panel"
  "equal or unequal response does not identify a regime without proximal target-engagement evidence"

mediatorNode : CausalMaintenanceParetoNode
mediatorNode = causal-maintenance-pareto-node
  "causal mediator identification" mediatorIdentificationNeeded Snowball.experimentalDesign
  "CausalEffectEstimandExact mediation surface"
  "current associations/predictors are not controlled direct or mediated indirect effects"
  "predeclare mediator, intervention, comparator, population and time; measure mediator before distal outcome where design permits"
  "candidate pathway label is not a mediation receipt"

transportNode : CausalMaintenanceParetoNode
transportNode = causal-maintenance-pareto-node
  "held-out maintenance-regime transport" externalTransportNeeded Snowball.externalKnowledgeComparison
  "current cohorts and intervention studies are assay/population/context specific"
  "regime discriminator may fail across diet, geography, sex, infection history, assay or treatment context"
  "held-out multi-site validation of the full discrimination contract and treatment interactions"
  "successful internal discrimination does not automatically transport"

canonicalCausalMaintenanceParetoFrontier : List CausalMaintenanceParetoNode
canonicalCausalMaintenanceParetoFrontier =
  autonomicPredictionNode ∷ brainGutTrialDesignNode ∷ neuromodulationNode ∷
  orthogonalProbeNode ∷ mediatorNode ∷ transportNode ∷ []

record IBSCausalMaintenanceBoundary : Set where
  constructor ibs-causal-maintenance-boundary
  field
    wholeSystemOwner : Whole.IBSWholeSystemBoundary
    transitionOwner : Transition.IBSLatentStateTransitionBoundary
    probeOwner : Probe.IBSMechanismProbeBoundary
    candidateRegimesAreHypotheses : Bool
    symptomSubtypeDefinesRegime : Bool
    predictiveBiomarkerDefinesMediator : Bool
    singleTreatmentResponseDefinesRegime : Bool
    causalEstimandMustRemainExplicit : Bool
    multiFibreLongitudinalPerturbationPreferred : Bool
    participantClassifierValidated : Bool

canonicalIBSCausalMaintenanceBoundary : IBSCausalMaintenanceBoundary
canonicalIBSCausalMaintenanceBoundary = ibs-causal-maintenance-boundary
  Whole.canonicalIBSWholeSystemBoundary Transition.canonicalIBSLatentStateTransitionBoundary
  Probe.canonicalIBSMechanismProbeBoundary true false false false true true false
