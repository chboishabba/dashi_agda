module DASHI.Biology.IBSSystemsIdentificationParetoExact where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.IBSGutBrainImmuneSystemsHyperfabricExact as IBS
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Snowball
import DASHI.Core.SelectiveInvalidationParetoFrontierBidiExact as Pareto
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Design

------------------------------------------------------------------------
-- IBS SYSTEMS IDENTIFICATION / PARETO ACQUISITION
--
-- The consumer is not "find one IBS biomarker". It is to distinguish competing
-- coupled gut/immune/neural system states and interventions with the smallest
-- evidence set that still separates relevant fibres. Numeric information gain
-- is not invented here; the frontier is qualitative/source-bounded.
------------------------------------------------------------------------

jacobs2023Source : Source.AttributedSource
jacobs2023Source = Source.mkDOISource
  "Jonathan P Jacobs et al."
  "Multi-omics profiles of the intestinal microbiome in irritable bowel syndrome and its bowel habit subtypes"
  "Microbiome 11:5" "2023"
  "10.1186/s40168-022-01450-5"
  "https://doi.org/10.1186/s40168-022-01450-5"
  Source.academicArticleSource
  "Pays a 495-participant multi-omics IBS/healthy-control cohort with 16S, metatranscriptomic and untargeted-metabolomic surfaces. Functional microbial profiles add information beyond composition; they do not identify a universal IBS mechanism or stable individual attractor."
  Source.publicAttribution

goyal2026Source : Source.AttributedSource
goyal2026Source = Source.mkDOISource
  "Manjeet Kumar Goyal; Omesh Goyal; Rishi Chowdhary; Tanisha Sehgal et al."
  "Biomarkers in Irritable Bowel Syndrome: Bridging Gut-Brain Mechanisms to Precision Care"
  "Current Gastroenterology Reports 28:25" "2026"
  "10.1007/s11894-026-01053-2"
  "https://doi.org/10.1007/s11894-026-01053-2"
  Source.academicArticleSource
  "Review-level support for replacing single-marker aspirations with multidimensional mechanism-based panels spanning inflammatory, microbial, metabolic and permeability domains; review synthesis is not a validated diagnostic panel by itself."
  Source.publicAttribution

bai2026Source : Source.AttributedSource
bai2026Source = Source.mkDOISource
  "Yuanzhen Bai; Meilin Yu; Chunyan Weng; Jingli Xu; Mingxu Zheng; Bin Lv"
  "Autonomic nervous system dysfunction in irritable bowel syndrome: pathophysiology and therapeutic implications"
  "Frontiers in Neuroscience 20:1832540" "2026"
  "10.3389/fnins.2026.1832540"
  "https://doi.org/10.3389/fnins.2026.1832540"
  Source.academicArticleSource
  "Review-level support for autonomic dysfunction as a bidirectional gut-brain coordinate interacting with stress, microbiota, neuroimmune signalling and visceral hypersensitivity. HRV or vagal tone is not promoted to the complete IBS state."
  Source.publicAttribution

diciaula2024Source : Source.AttributedSource
diciaula2024Source = Source.mkDOISource
  "Agostino Di Ciaula; Mohamad Khalil; Gyorgy Baffy; Piero Portincasa"
  "Advances in the pathophysiology, diagnosis and management of chronic diarrhoea from bile acid malabsorption: a systematic review"
  "European Journal of Internal Medicine 128:10-19" "2024"
  "10.1016/j.ejim.2024.07.008"
  "https://doi.org/10.1016/j.ejim.2024.07.008"
  Source.academicArticleSource
  "Systematic-review support for a bile-acid diarrhoea mechanism involving hepatic/gut synthesis and metabolism, microbiota, enterohepatic circulation and FXR/FGFR4/GPBAR1 signalling. This mechanism overlaps IBS-D presentations but is not identical to all IBS-D."
  Source.publicAttribution

data MeasurementAxis : Set where
  symptomTrajectoryAxis : MeasurementAxis
  bowelHabitTransitAxis : MeasurementAxis
  microbiomeCompositionAxis : MeasurementAxis
  microbiomeFunctionAxis : MeasurementAxis
  metabolomeAxis : MeasurementAxis
  histamineMastCellAxis : MeasurementAxis
  immuneInflammatoryAxis : MeasurementAxis
  epithelialBarrierAxis : MeasurementAxis
  bileAcidAxis : MeasurementAxis
  autonomicAxis : MeasurementAxis
  endocrineHPAaxis : MeasurementAxis
  visceralSensitivityAxis : MeasurementAxis
  centralInteroceptivePainAxis : MeasurementAxis
  dietExposureAxis : MeasurementAxis

data MeasurementRole : Set where
  diagnosticExclusionRole : MeasurementRole
  mechanismStratificationRole : MeasurementRole
  longitudinalStateRole : MeasurementRole
  perturbationResponseRole : MeasurementRole
  nuisanceControlRole : MeasurementRole

record MeasurementCoordinate : Set where
  constructor measurement-coordinate
  field
    axis : MeasurementAxis
    role : MeasurementRole
    sourceReference : String
    measuredSurface : String
    doesNotIdentify : String
open MeasurementCoordinate public

canonicalIBSMeasurementAtlas : List MeasurementCoordinate
canonicalIBSMeasurementAtlas =
  measurement-coordinate microbiomeFunctionAxis mechanismStratificationRole
    "Jacobs 2023, DOI 10.1186/s40168-022-01450-5"
    "metatranscriptomic microbial function"
    "microbial functional profile does not by itself identify whole-system causal state" ∷
  measurement-coordinate metabolomeAxis mechanismStratificationRole
    "Jacobs 2023, DOI 10.1186/s40168-022-01450-5"
    "untargeted fecal metabolome"
    "metabolite profile does not identify source organism, host response or direction of causality" ∷
  measurement-coordinate immuneInflammatoryAxis mechanismStratificationRole
    "Goyal 2026 biomarker synthesis; existing IBS histamine/mast-cell tranche"
    "cytokine/inflammatory and mast-cell-related measurements"
    "low-grade immune activation is not the complete IBS mechanism" ∷
  measurement-coordinate epithelialBarrierAxis longitudinalStateRole
    "Goyal 2026 plus Gao mechanistic IBS-D diet trial already acquired"
    "permeability/barrier-related measures"
    "barrier change does not identify whether diet, immune, microbial or autonomic route generated it" ∷
  measurement-coordinate bileAcidAxis mechanismStratificationRole
    "Di Ciaula 2024, DOI 10.1016/j.ejim.2024.07.008"
    "bile-acid synthesis/transport/metabolism phenotype"
    "bile-acid diarrhoea mechanism does not equal all IBS-D" ∷
  measurement-coordinate autonomicAxis longitudinalStateRole
    "Bai 2026, DOI 10.3389/fnins.2026.1832540"
    "autonomic/vagal-sympathetic dynamics such as appropriately controlled HRV-related measures"
    "autonomic marker is not full allostatic or IBS state" ∷
  measurement-coordinate visceralSensitivityAxis perturbationResponseRole
    "IBS whole-system hyperfabric and H1/TRPV1 intervention lane"
    "visceral sensory gain / pain response"
    "symptom sensitivity does not identify upstream mediator" ∷
  measurement-coordinate symptomTrajectoryAxis longitudinalStateRole
    "positive symptom-based IBS diagnosis and repeated outcome trajectory"
    "pain, urgency, stool-form and quality-of-life trajectory"
    "symptom trajectory is an output projection, not a mechanism label" ∷ []

------------------------------------------------------------------------
-- Identifiability firewalls.
------------------------------------------------------------------------

data SingleMarkerIdentifiesWholeSystemStatePermission : Set where
singleMarkerDoesNotIdentifyWholeSystemState :
  SingleMarkerIdentifiesWholeSystemStatePermission → ⊥
singleMarkerDoesNotIdentifyWholeSystemState ()

data BowelHabitSubtypeIdentifiesMechanismPermission : Set where
bowelHabitSubtypeDoesNotIdentifyMechanism :
  BowelHabitSubtypeIdentifiesMechanismPermission → ⊥
bowelHabitSubtypeDoesNotIdentifyMechanism ()

data CrossSectionIdentifiesFeedbackDirectionPermission : Set where
crossSectionDoesNotIdentifyFeedbackDirection :
  CrossSectionIdentifiesFeedbackDirectionPermission → ⊥
crossSectionDoesNotIdentifyFeedbackDirection ()

data CorrelatedOmicsIdentifiesCausalLoopPermission : Set where
correlatedOmicsDoesNotIdentifyCausalLoop :
  CorrelatedOmicsIdentifiesCausalLoopPermission → ⊥
correlatedOmicsDoesNotIdentifyCausalLoop ()

------------------------------------------------------------------------
-- Minimal discriminating panel: qualitative design, not validated clinical
-- instrument. Each axis is chosen because it separates a live system fibre.
------------------------------------------------------------------------

record DiscriminatingPanel : Set where
  constructor discriminating-panel
  field
    repeatedSymptoms : MeasurementAxis
    stoolOrTransit : MeasurementAxis
    microbialFunction : MeasurementAxis
    metabolome : MeasurementAxis
    immuneMastCell : MeasurementAxis
    barrier : MeasurementAxis
    bileAcid : MeasurementAxis
    autonomic : MeasurementAxis
    visceralSensitivity : MeasurementAxis
    exposureLedger : MeasurementAxis
    longitudinalRepeatedMeasuresRequired : Bool
    controlledPerturbationPreferredForDirection : Bool
    panelIsValidatedClinicalDiagnostic : Bool
open DiscriminatingPanel public

canonicalMinimumDiscriminatingPanel : DiscriminatingPanel
canonicalMinimumDiscriminatingPanel = discriminating-panel
  symptomTrajectoryAxis bowelHabitTransitAxis microbiomeFunctionAxis metabolomeAxis
  histamineMastCellAxis epithelialBarrierAxis bileAcidAxis autonomicAxis
  visceralSensitivityAxis dietExposureAxis
  true true false

------------------------------------------------------------------------
-- Pareto acquisition frontier.
------------------------------------------------------------------------

data AcquisitionStatus : Set where
  acquiredStructuralEvidence : AcquisitionStatus
  acquiredCohortEvidence : AcquisitionStatus
  longitudinalAcquisitionNeeded : AcquisitionStatus
  perturbationAcquisitionNeeded : AcquisitionStatus
  replicationAcquisitionNeeded : AcquisitionStatus

data InformationValue : Set where
  separatesOneFibre : InformationValue
  separatesSeveralFibres : InformationValue
  directionSensitive : InformationValue
  transportSensitive : InformationValue
  stateTransitionSensitive : InformationValue

record SystemsAcquisitionNode : Set where
  constructor systems-acquisition-node
  field
    label : String
    status : AcquisitionStatus
    route : Snowball.DiscoveryRoute
    value : InformationValue
    paidReference : String
    residual : String
    authorityBoundary : String
open SystemsAcquisitionNode public

multiOmicsFunctionNode : SystemsAcquisitionNode
multiOmicsFunctionNode = systems-acquisition-node
  "microbiome function + metabolome"
  acquiredCohortEvidence Snowball.externalKnowledgeComparison separatesSeveralFibres
  "Jacobs 2023 multi-omics cohort"
  "needs repeated within-person sampling and perturbation to infer state transitions/direction"
  "cohort association is not a causal-loop identifier"

compositeBiomarkerNode : SystemsAcquisitionNode
compositeBiomarkerNode = systems-acquisition-node
  "composite mechanism-based biomarker panel"
  acquiredStructuralEvidence Snowball.externalKnowledgeComparison separatesSeveralFibres
  "Goyal 2026 review synthesis"
  "requires prospective validation, calibration and treatment-response usefulness"
  "review-proposed panel logic is not a validated clinical classifier"

autonomicDynamicsNode : SystemsAcquisitionNode
autonomicDynamicsNode = systems-acquisition-node
  "autonomic dynamics"
  acquiredStructuralEvidence Snowball.externalKnowledgeComparison stateTransitionSensitive
  "Bai 2026 ANS review plus existing allostatic/interoception owners"
  "needs synchronized repeated autonomic, gut and symptom measurements under controlled context"
  "HRV/vagal measures are proxy coordinates, not complete autonomic state"

bileAcidMechanismNode : SystemsAcquisitionNode
bileAcidMechanismNode = systems-acquisition-node
  "bile-acid physiology in diarrhoeal presentations"
  acquiredStructuralEvidence Snowball.externalKnowledgeComparison separatesOneFibre
  "Di Ciaula 2024 systematic review"
  "needs explicit differential/overlap handling against IBS-D, transit, microbiome and dietary fibres"
  "bile-acid diarrhoea is a mechanism/differential, not synonymous with IBS-D"

withinPersonStateTransitionNode : SystemsAcquisitionNode
withinPersonStateTransitionNode = systems-acquisition-node
  "within-person multi-fibre state transition"
  longitudinalAcquisitionNeeded Snowball.experimentalDesign stateTransitionSensitive
  "whole-system hyperfabric exposes recurrent state ambiguity"
  "dense repeated symptom + diet + stool/metabolome + immune/barrier + autonomic measurements around flares/remissions"
  "longitudinal association still requires perturbation or identification assumptions for causal direction"

controlledPerturbationNode : SystemsAcquisitionNode
controlledPerturbationNode = systems-acquisition-node
  "mechanism-selective perturbation with multi-fibre readout"
  perturbationAcquisitionNeeded Snowball.experimentalDesign directionSensitive
  "experimental-design backprop from competing feedback loops"
  "cross-over or randomized perturbations chosen to target distinct fibres, with matched longitudinal panel and washout/context control"
  "response to one perturbation does not prove uniqueness of the targeted mechanism"

externalReplicationNode : SystemsAcquisitionNode
externalReplicationNode = systems-acquisition-node
  "external replication of discovered system-state signatures"
  replicationAcquisitionNeeded Snowball.externalKnowledgeComparison transportSensitive
  "multi-omics / biomarker signatures remain cohort- and pipeline-sensitive"
  "multi-site held-out validation across geography, diet, sex, subtype and assay pipeline"
  "replication transports a signature only within demonstrated populations/pipelines"

canonicalIBSSystemsParetoFrontier : List SystemsAcquisitionNode
canonicalIBSSystemsParetoFrontier =
  multiOmicsFunctionNode ∷ compositeBiomarkerNode ∷ autonomicDynamicsNode ∷
  bileAcidMechanismNode ∷ withinPersonStateTransitionNode ∷
  controlledPerturbationNode ∷ externalReplicationNode ∷ []

record IBSSystemsIdentificationBoundary : Set where
  constructor ibs-systems-identification-boundary
  field
    wholeSystemOwner : IBS.IBSWholeSystemBoundary
    paretoOwner : Pareto.RecursiveParetoCompatibility
    singleMarkerSufficient : Bool
    bowelHabitSubtypeSufficientMechanismLabel : Bool
    crossSectionSufficientForFeedbackDirection : Bool
    repeatedMultifibreMeasurementPreferred : Bool
    perturbationNeededForDirectionWithoutStrongIdentificationAssumptions : Bool
    clinicalPanelValidationClaimed : Bool
    numericalInformationGainInvented : Bool

canonicalIBSSystemsIdentificationBoundary : IBSSystemsIdentificationBoundary
canonicalIBSSystemsIdentificationBoundary = ibs-systems-identification-boundary
  IBS.canonicalIBSWholeSystemBoundary
  Pareto.canonicalRecursiveParetoCompatibility
  false false false true true false false
