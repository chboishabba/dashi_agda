module DASHI.Biology.IBSMonashAdaptiveSequencingExact where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.IBSResponsePredictorAtlasExact as Predictor
import DASHI.Biology.IBSCausalMaintenanceRegimeExact as Regime
import DASHI.Biology.IBSMechanismProbePerturbationAtlasExact as Probe
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Snowball

------------------------------------------------------------------------
-- MONASH IBS/FODMAP PROGRAMME + ADAPTIVE SEQUENCING
--
-- Attribution rule: each source pays only its reported intervention,
-- physiological or association surface. "Monash programme" is a provenance
-- grouping, not a theorem-authority bundle. Adaptive sequencing below is a
-- qualitative experimental-design surface; no numeric utility is invented.
------------------------------------------------------------------------

halmos2014Source : Source.AttributedSource
halmos2014Source = Source.mkDOISource
  "Emma P Halmos; Victoria A Power; Susan J Shepherd; Peter R Gibson; Jane G Muir"
  "A diet low in FODMAPs reduces symptoms of irritable bowel syndrome"
  "Gastroenterology 146(1):67-75.e5" "2014"
  "10.1053/j.gastro.2013.09.046"
  "https://doi.org/10.1053/j.gastro.2013.09.046"
  Source.academicArticleSource
  "Monash-affiliated randomized controlled single-blind crossover evidence that a low-FODMAP diet reduced IBS symptoms versus a typical Australian diet in the studied cohort. It does not identify a unique causal mechanism or universal responder class."
  Source.publicAttribution

halmos2015LuminalSource : Source.AttributedSource
halmos2015LuminalSource = Source.mkDOISource
  "Emma P Halmos; Claus T Christophersen; Anthony R Bird; Susan J Shepherd; Peter R Gibson; Jane G Muir"
  "Diets that differ in their FODMAP content alter the colonic luminal microenvironment"
  "Gut 64(1):93-100" "2015"
  "10.1136/gutjnl-2014-307264"
  "https://doi.org/10.1136/gutjnl-2014-307264"
  Source.academicArticleSource
  "Randomized crossover evidence that changing dietary FODMAP content altered luminal microbial/metabolic ecology. Ecological change is not by itself a mediation proof for symptom change."
  Source.publicAttribution

peters2016Source : Source.AttributedSource
peters2016Source = Source.mkDOISource
  "S L Peters; C K Yao; H Philpott; G W Yelland; J G Muir; P R Gibson"
  "Randomised clinical trial: the efficacy of gut-directed hypnotherapy is similar to that of the low FODMAP diet for the treatment of irritable bowel syndrome"
  "Alimentary Pharmacology & Therapeutics 44(5):447-459" "2016"
  "10.1111/apt.13706"
  "https://doi.org/10.1111/apt.13706"
  Source.academicArticleSource
  "Monash/Alfred randomized comparison of gut-directed hypnotherapy, low-FODMAP diet and combination. Similar GI symptom improvement across mechanistically distinct interventions blocks response-equals-mechanism inference."
  Source.publicAttribution

tuck2018GOSSource : Source.AttributedSource
tuck2018GOSSource = Source.mkDOISource
  "Caroline J Tuck; K M Taylor; Peter R Gibson; Jacqueline S Barrett; Jane G Muir"
  "Increasing Symptoms in Irritable Bowel Syndrome With Ingestion of Galacto-Oligosaccharides Are Mitigated by alpha-Galactosidase Treatment"
  "American Journal of Gastroenterology 113(1):124-134" "2018"
  "10.1038/ajg.2017.245"
  "https://doi.org/10.1038/ajg.2017.245"
  Source.academicArticleSource
  "Monash randomized double-blind placebo-controlled crossover evidence using GOS challenge and alpha-galactosidase co-treatment. This is a nutrient-specific perturbation/rescue surface, not proof that all FODMAP responses share that mechanism."
  Source.publicAttribution

silva2026Source : Source.AttributedSource
silva2026Source = Source.mkDOISource
  "Hannah Silva; Tenghao Zheng; Judi Porter; Jacqueline Barrett; Mayur Garg; Peter R Gibson"
  "The Associations of Sucrase-Isomaltase Hypomorphic Variants With Long-Term Outcomes and Dietary Intake in an Australian Irritable Bowel Syndrome Population Educated on the FODMAP Diet"
  "United European Gastroenterology Journal 14(1):e70173" "2026"
  "10.1002/ueg2.70173"
  "https://doi.org/10.1002/ueg2.70173"
  Source.academicArticleSource
  "Monash-linked retrospective cohort testing sucrase-isomaltase hypomorphic variants as a possible modifier after FODMAP education. Single-variant carriage was not associated with initial FODMAP response, long-term symptom control, or current sucrose/starch intake in the represented cohort. This negative stratification result is not universal genetic irrelevance."
  Source.publicAttribution

data MonashEvidenceRole : Set where
  wholeDietEfficacy : MonashEvidenceRole
  luminalEcologyPerturbation : MonashEvidenceRole
  orthogonalTherapyComparison : MonashEvidenceRole
  nutrientChallengeRescue : MonashEvidenceRole
  digestiveGeneticModifier : MonashEvidenceRole

record MonashIBSEvidence : Set where
  constructor monash-ibs-evidence
  field
    source : Source.AttributedSource
    role : MonashEvidenceRole
    interventionOrExposure : String
    observedSurface : String
    mechanismIdentified : Bool
    participantClassifierValidated : Bool
open MonashIBSEvidence public

canonicalMonashIBSProgrammeAtlas : List MonashIBSEvidence
canonicalMonashIBSProgrammeAtlas =
  monash-ibs-evidence halmos2014Source wholeDietEfficacy
    "low-FODMAP versus Australian diet crossover"
    "IBS symptom response"
    false false ∷
  monash-ibs-evidence halmos2015LuminalSource luminalEcologyPerturbation
    "controlled dietary FODMAP-content change"
    "colonic luminal microbial/metabolic environment"
    false false ∷
  monash-ibs-evidence peters2016Source orthogonalTherapyComparison
    "gut-directed hypnotherapy versus low-FODMAP versus combination"
    "GI and psychological outcomes"
    false false ∷
  monash-ibs-evidence tuck2018GOSSource nutrientChallengeRescue
    "GOS challenge with alpha-galactosidase versus placebo"
    "nutrient-specific symptom provocation/rescue"
    false false ∷
  monash-ibs-evidence silva2026Source digestiveGeneticModifier
    "single sucrase-isomaltase hypomorphic-variant status after FODMAP education"
    "negative stratification result for initial response, long-term symptom control and sucrose/starch intake in the represented cohort"
    false false ∷ []

data TreatmentResponseIdentifiesMechanismPermission : Set where
treatmentResponseDoesNotIdentifyMechanism : TreatmentResponseIdentifiesMechanismPermission → ⊥
treatmentResponseDoesNotIdentifyMechanism ()

data InformationGainEqualsClinicalBenefitPermission : Set where
informationGainDoesNotEqualClinicalBenefit : InformationGainEqualsClinicalBenefitPermission → ⊥
informationGainDoesNotEqualClinicalBenefit ()

data LowFODMAPResponseIdentifiesUniversalFODMAPMechanismPermission : Set where
lowFODMAPResponseDoesNotIdentifyUniversalMechanism :
  LowFODMAPResponseIdentifiesUniversalFODMAPMechanismPermission → ⊥
lowFODMAPResponseDoesNotIdentifyUniversalMechanism ()

------------------------------------------------------------------------
-- Qualitative adaptive sequencing. The selector balances therapeutic value,
-- discrimination value, burden and safety; it does not manufacture expected
-- utilities or recommend a clinical sequence for a specific person.
------------------------------------------------------------------------

data TherapeuticValue : Set where
  establishedTreatmentValue : TherapeuticValue
  boundedTreatmentValue : TherapeuticValue
  probeOnlyValue : TherapeuticValue

data DiscriminationValue : Set where
  lowDiscrimination : DiscriminationValue
  separatesOneFibre : DiscriminationValue
  separatesOrthogonalFibres : DiscriminationValue
  transitionSensitive : DiscriminationValue

data BurdenClass : Set where
  lowBurden : BurdenClass
  moderateBurden : BurdenClass
  highBurden : BurdenClass

data AdaptiveAction : Set where
  lowFODMAPAction : AdaptiveAction
  blindedFODMAPRechallengeAction : AdaptiveAction
  gutDirectedHypnotherapyAction : AdaptiveAction
  rifaximinAction : AdaptiveAction
  bileAcidProbeAction : AdaptiveAction
  histamineH1ProbeAction : AdaptiveAction
  quailCandidateProbeAction : AdaptiveAction

record AdaptiveTreatmentProbe : Set where
  constructor adaptive-treatment-probe
  field
    action : AdaptiveAction
    therapeuticValue : TherapeuticValue
    discriminationValue : DiscriminationValue
    burden : BurdenClass
    proximalReadout : String
    distalReadout : String
    attributionBoundary : String
open AdaptiveTreatmentProbe public

lowFODMAPAdaptiveProbe : AdaptiveTreatmentProbe
lowFODMAPAdaptiveProbe = adaptive-treatment-probe
  lowFODMAPAction establishedTreatmentValue separatesOrthogonalFibres moderateBurden
  "diet exposure/adherence + fermentation/luminal ecology"
  "symptom trajectory"
  "response does not identify whether osmotic, fermentative, microbial, sensory, expectancy or mixed path dominates"

rechallengeAdaptiveProbe : AdaptiveTreatmentProbe
rechallengeAdaptiveProbe = adaptive-treatment-probe
  blindedFODMAPRechallengeAction probeOnlyValue transitionSensitive moderateBurden
  "within-person class-specific challenge response and latency"
  "symptom recurrence/recovery trajectory"
  "trigger identification does not identify downstream mechanism or universal intolerance"

hypnotherapyAdaptiveProbe : AdaptiveTreatmentProbe
hypnotherapyAdaptiveProbe = adaptive-treatment-probe
  gutDirectedHypnotherapyAction establishedTreatmentValue separatesOrthogonalFibres moderateBurden
  "central/interoceptive and autonomic response surface where measured"
  "symptom/QOL trajectory"
  "clinical response does not prove central-only maintenance"

record AdaptiveSequencingNode : Set where
  constructor adaptive-sequencing-node
  field
    label : String
    route : Snowball.DiscoveryRoute
    currentEvidence : String
    informationDebt : String
    nextDesign : String
    authorityBoundary : String
open AdaptiveSequencingNode public

canonicalAdaptiveTreatmentSequencingFrontier : List AdaptiveSequencingNode
canonicalAdaptiveTreatmentSequencingFrontier =
  adaptive-sequencing-node
    "orthogonal diet versus brain-gut intervention"
    Snowball.externalKnowledgeComparison
    "Peters 2016 Monash RCT supplies mechanistically distinct interventions with overlapping symptom benefit"
    "need synchronized peripheral/central target-engagement measurements to determine propagation patterns"
    "factorial or sequential design with common whole-system panel and recovery interval"
    "similar efficacy does not imply common mechanism" ∷
  adaptive-sequencing-node
    "nutrient-specific challenge-rescue"
    Snowball.externalKnowledgeComparison
    "Tuck 2018 GOS challenge plus alpha-galactosidase rescue"
    "need transport to other FODMAP classes and explicit fermentation/osmotic/sensory readouts"
    "class-specific blinded challenges with matched rescue where a mechanistically valid rescue exists"
    "one carbohydrate-rescue result does not generalize to all FODMAPs" ∷
  adaptive-sequencing-node
    "adaptive therapy as identification experiment"
    Snowball.experimentalDesign
    "current Regime/Predictor/Probe owners provide competing hypotheses and treatment-specific signals"
    "no validated policy combines therapeutic value, information value, burden and uncertainty"
    "prospective SMART-like or response-adaptive trial with locked switching rules, proximal target engagement and patient-centred outcomes"
    "an informative probe is not necessarily the clinically best treatment, and clinical benefit is not information gain" ∷
  adaptive-sequencing-node
    "SI genotype negative-stratification"
    Snowball.externalKnowledgeComparison
    "Silva 2026 found no association of single SI hypomorphic variants with initial or long-term FODMAP outcomes in the represented cohort"
    "double-carriers were sparse and retrospective ascertainment limits broader inference"
    "prospective genotype-by-diet interaction only if this residual remains decision-relevant"
    "negative single-variant result blocks a positive modifier claim but does not prove universal genetic irrelevance" ∷ []

record MonashAdaptiveBoundary : Set where
  constructor monash-adaptive-boundary
  field
    monashSourcesGroupedByProvenanceNotAuthority : Bool
    responseMechanismSeparated : Bool
    benefitInformationSeparated : Bool
    burdenRetained : Bool
    noNumericUtilityInvented : Bool
    noPatientSpecificSequenceClaimed : Bool
    regimeOwner : Regime.IBSCausalMaintenanceBoundary
    predictorOwner : Predictor.IBSResponsePredictorBoundary
    probeOwner : Probe.IBSMechanismProbeBoundary

canonicalMonashAdaptiveBoundary : MonashAdaptiveBoundary
canonicalMonashAdaptiveBoundary = monash-adaptive-boundary
  true true true true true true
  Regime.canonicalIBSCausalMaintenanceBoundary
  Predictor.canonicalIBSResponsePredictorBoundary
  Probe.canonicalIBSMechanismProbeBoundary