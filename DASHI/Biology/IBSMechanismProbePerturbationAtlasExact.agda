module DASHI.Biology.IBSMechanismProbePerturbationAtlasExact where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.IBSSystemsIdentificationParetoExact as Systems
import DASHI.Biology.IBSGutBrainImmuneSystemsHyperfabricExact as Whole
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Snowball

------------------------------------------------------------------------
-- MECHANISM-SELECTIVE PERTURBATIONS AS SYSTEM PROBES
--
-- Treatment response is useful evidence about a coupled system, but it is not
-- a unique inverse map from outcome to mechanism. Orthogonal perturbations are
-- retained as probes of different fibres while common symptom endpoints allow
-- comparison without collapsing mechanisms.
------------------------------------------------------------------------

lee2026Source : Source.AttributedSource
lee2026Source = Source.mkDOISource
  "Allen A Lee; Krishna Rao; Prashant Singh et al."
  "A Randomized Trial of Rifaximin vs Low Fermentable Oligosaccharides, Disaccharides, Monosaccharides, and Polyols Diet for Symptom Outcomes and Microbiome Changes in Irritable Bowel Syndrome"
  "Clinical Gastroenterology and Hepatology" "2026"
  "10.1016/j.cgh.2026.04.014"
  "https://doi.org/10.1016/j.cgh.2026.04.014"
  Source.academicArticleSource
  "Randomized IBS-D comparison of two mechanistically different interventions, low-FODMAP diet and rifaximin, with repeated symptoms, stool microbiome and breath testing. Both improved symptoms while baseline taxa associated differently with response; this is evidence for heterogeneous response surfaces, not unique mechanism identification."
  Source.publicAttribution

fODMAPReintroduction2024Source : Source.AttributedSource
fODMAPReintroduction2024Source = Source.mkDOISource
  "authors as indexed by Gastroenterology"
  "Efficacy and Findings of a Blinded Randomized Reintroduction Phase for the Low FODMAP Diet in Irritable Bowel Syndrome"
  "Gastroenterology" "2024"
  "10.1053/j.gastro.2024.02.008"
  "https://doi.org/10.1053/j.gastro.2024.02.008"
  Source.academicArticleSource
  "Pays blinded randomized reintroduction of individual FODMAP classes after response to restriction, allowing within-person dietary trigger discrimination. Trigger response is not a universal intolerance label or a complete IBS mechanism."
  Source.publicAttribution

colesevelam2020Source : Source.AttributedSource
colesevelam2020Source = Source.mkDOISource
  "Michael Camilleri et al."
  "Effects of Colesevelam on Bowel Symptoms, Biomarkers, and Colonic Mucosal Gene Expression in Patients With Bile Acid Diarrhea in a Randomized Trial"
  "Clinical Gastroenterology and Hepatology" "2020"
  "10.1016/j.cgh.2020.02.021"
  "https://doi.org/10.1016/j.cgh.2020.02.021"
  Source.academicArticleSource
  "Randomized mechanistic bile-acid-sequestration probe in IBS-D participants selected for bile-acid diarrhoea evidence, with fecal bile acids, C4, FGF19, transit, permeability and mucosal gene-expression readouts. Biological target engagement did not automatically translate into broad symptom/transit differences in the small trial."
  Source.publicAttribution

lowen2013Source : Source.AttributedSource
lowen2013Source = Source.mkDOISource
  "Mats B O Lowen; Emeran A Mayer; M Sjoberg; Kirsten Tillisch; Bruce Naliboff; Jennifer Labus; Peter Lundberg; Magnus Strom; Maria Engstrom; Susanna A Walter"
  "Effect of hypnotherapy and educational intervention on brain response to visceral stimulus in the irritable bowel syndrome"
  "Alimentary Pharmacology & Therapeutics 37(12):1184-1197" "2013"
  "10.1111/apt.12319"
  "https://doi.org/10.1111/apt.12319"
  Source.academicArticleSource
  "Pays a central/interoceptive perturbation surface: successful treatment was associated with altered fMRI response to rectal distension, including anterior-insula attenuation. Similar symptom improvement across intervention groups prevents simple treatment-mechanism identity."
  Source.publicAttribution

data ProbeFibre : Set where
  dietaryFermentationProbe : ProbeFibre
  microbiomeAntibioticProbe : ProbeFibre
  bileAcidProbe : ProbeFibre
  centralInteroceptiveProbe : ProbeFibre
  histamineH1Probe : ProbeFibre
  quailMastCellCandidateProbe : ProbeFibre

data ProbeEvidenceClass : Set where
  randomizedComparative : ProbeEvidenceClass
  randomizedBlindedChallenge : ProbeEvidenceClass
  randomizedMechanistic : ProbeEvidenceClass
  interventionWithImaging : ProbeEvidenceClass
  adjacentBoundedEvidence : ProbeEvidenceClass

record MechanismProbe : Set where
  constructor mechanism-probe
  field
    fibre : ProbeFibre
    evidenceClass : ProbeEvidenceClass
    source : Source.AttributedSource
    perturbation : String
    proximalReadout : String
    distalReadout : String
    interpretation : String
    uniqueMechanismIdentified : Bool
open MechanismProbe public

lowFODMAPProbe : MechanismProbe
lowFODMAPProbe = mechanism-probe dietaryFermentationProbe randomizedComparative lee2026Source
  "low-FODMAP dietary substrate restriction"
  "microbiome composition / fermentation-linked ecological response"
  "pain, bloating and IBS severity trajectory"
  "tests a diet/substrate-microbiome fibre but response can propagate through metabolite, immune, sensory and central routes"
  false

rifaximinProbe : MechanismProbe
rifaximinProbe = mechanism-probe microbiomeAntibioticProbe randomizedComparative lee2026Source
  "rifaximin"
  "microbial ecological response"
  "pain, bloating and IBS severity trajectory"
  "mechanistically distinct from dietary substrate restriction despite overlapping clinical endpoints"
  false

fODMAPChallengeProbe : MechanismProbe
fODMAPChallengeProbe = mechanism-probe dietaryFermentationProbe randomizedBlindedChallenge fODMAPReintroduction2024Source
  "blinded individual FODMAP-class reintroduction"
  "within-person trigger response"
  "IBS-SSS and symptom trajectory"
  "high information value for individual exposure sensitivity while remaining downstream-mechanism ambiguous"
  false

bileAcidSequestrationProbe : MechanismProbe
bileAcidSequestrationProbe = mechanism-probe bileAcidProbe randomizedMechanistic colesevelam2020Source
  "colesevelam bile-acid sequestration"
  "fecal bile acids, serum C4/FGF19 and mucosal bile-acid receptor gene expression"
  "stool, transit and permeability endpoints"
  "strong target-engagement probe for a selected bile-acid fibre; lack of broad clinical difference in a small study blocks target-engagement=whole-symptom-closure"
  false

centralInteroceptiveProbe : MechanismProbe
centralInteroceptiveProbe = mechanism-probe centralInteroceptiveProbe interventionWithImaging lowen2013Source
  "gut-directed hypnotherapy / educational intervention"
  "fMRI response during expected and delivered rectal distension"
  "symptom response"
  "central pain/interoception changes can accompany clinical response without proving that central change is the unique upstream cause"
  false

canonicalIBSMechanismProbeAtlas : List MechanismProbe
canonicalIBSMechanismProbeAtlas =
  lowFODMAPProbe ∷ rifaximinProbe ∷ fODMAPChallengeProbe ∷
  bileAcidSequestrationProbe ∷ centralInteroceptiveProbe ∷ []

data ResponseIdentifiesUniqueMechanismPermission : Set where
responseDoesNotIdentifyUniqueMechanism : ResponseIdentifiesUniqueMechanismPermission → ⊥
responseDoesNotIdentifyUniqueMechanism ()

data EqualSymptomResponseMeansSamePathwayPermission : Set where
equalSymptomResponseDoesNotMeanSamePathway : EqualSymptomResponseMeansSamePathwayPermission → ⊥
equalSymptomResponseDoesNotMeanSamePathway ()

data TargetEngagementMeansWholeSystemClosurePermission : Set where
targetEngagementDoesNotMeanWholeSystemClosure : TargetEngagementMeansWholeSystemClosurePermission → ⊥
targetEngagementDoesNotMeanWholeSystemClosure ()

record ProbeParetoNode : Set where
  constructor probe-pareto-node
  field
    label : String
    route : Snowball.DiscoveryRoute
    separatesFibre : Whole.IBSSystemFibre
    proximalMeasurement : Systems.MeasurementAxis
    distalMeasurement : Systems.MeasurementAxis
    currentValue : String
    nextAcquisition : String
open ProbeParetoNode public

pairedDietRifaximinNode : ProbeParetoNode
pairedDietRifaximinNode = probe-pareto-node
  "diet-vs-rifaximin differential response"
  Snowball.externalKnowledgeComparison
  Whole.microbiomeMetaboliteFibre
  Systems.microbiomeFunctionAxis Systems.symptomTrajectoryAxis
  "randomized comparative perturbation with distinct baseline microbial response associations"
  "replicate with metatranscriptome/metabolome, barrier/immune and autonomic readouts to observe propagation beyond taxonomic shifts"

withinPersonFODMAPNode : ProbeParetoNode
withinPersonFODMAPNode = probe-pareto-node
  "within-person blinded dietary challenge"
  Snowball.externalKnowledgeComparison
  Whole.dietExposureFibre
  Systems.dietExposureAxis Systems.symptomTrajectoryAxis
  "randomized challenge identifies person-specific trigger classes"
  "add synchronized fermentation/metabolite, mast-cell/barrier and autonomic measurements to separate chemical exposure from downstream gain"

bileAcidProbeNode : ProbeParetoNode
bileAcidProbeNode = probe-pareto-node
  "bile-acid target-engagement probe"
  Snowball.externalKnowledgeComparison
  Whole.neurochemicalMetabolicFibre
  Systems.bileAcidAxis Systems.bowelHabitTransitAxis
  "direct biochemical target engagement with several physiological readouts"
  "larger target-positive cohorts with symptom response and competing-fibre panel"

centralProbeNode : ProbeParetoNode
centralProbeNode = probe-pareto-node
  "central/interoceptive perturbation probe"
  Snowball.externalKnowledgeComparison
  Whole.centralPainInteroceptiveFibre
  Systems.centralInteroceptivePainAxis Systems.symptomTrajectoryAxis
  "treatment-associated brain-response change during controlled visceral stimulation"
  "modern preregistered replication with autonomic, peripheral and symptom trajectories to test bidirectional propagation"

quailSystemsProbeNode : ProbeParetoNode
quailSystemsProbeNode = probe-pareto-node
  "quail local mast-cell candidate as whole-system probe"
  Snowball.experimentalDesign
  Whole.mucosalImmuneMastCellFibre
  Systems.histamineMastCellAxis Systems.symptomTrajectoryAxis
  "preclinical/local quail evidence is available but human IBS same-object perturbation remains open"
  "if tested, pair quail-specific exposure with mast-cell/histamine, barrier, metabolome/microbiome, autonomic, visceral-sensitivity and symptom trajectories"

canonicalIBSProbeParetoFrontier : List ProbeParetoNode
canonicalIBSProbeParetoFrontier =
  pairedDietRifaximinNode ∷ withinPersonFODMAPNode ∷ bileAcidProbeNode ∷
  centralProbeNode ∷ quailSystemsProbeNode ∷ []

record IBSMechanismProbeBoundary : Set where
  constructor ibs-mechanism-probe-boundary
  field
    orthogonalPerturbationsRetained : Bool
    commonClinicalEndpointsAllowComparison : Bool
    equalClinicalResponseImpliesSameMechanism : Bool
    proximalTargetEngagementImpliesWholeSystemClosure : Bool
    quailCanBeDesignedAsLocalProbeWithWholeSystemReadout : Bool

canonicalIBSMechanismProbeBoundary : IBSMechanismProbeBoundary
canonicalIBSMechanismProbeBoundary = ibs-mechanism-probe-boundary
  true true false false true
