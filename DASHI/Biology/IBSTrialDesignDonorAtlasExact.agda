module DASHI.Biology.IBSTrialDesignDonorAtlasExact where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Snowball

------------------------------------------------------------------------
-- TRIAL-DESIGN DONORS FOR ADAPTIVE IBS IDENTIFICATION
--
-- Method papers donate design structure only. IBS studies donate only their
-- reported outcome/measurement surfaces. Neither role imports the other.
------------------------------------------------------------------------

collins2007Source : Source.AttributedSource
collins2007Source = Source.mkDOISource
  "Linda M Collins; Susan A Murphy; Victor Strecher"
  "The multiphase optimization strategy (MOST) and the sequential multiple assignment randomized trial (SMART): new methods for more potent eHealth interventions"
  "American Journal of Preventive Medicine 32(5 Suppl):S112-S118" "2007"
  "10.1016/j.amepre.2007.01.022"
  "https://doi.org/10.1016/j.amepre.2007.01.022"
  Source.academicArticleSource
  "Methodological donor for prospectively randomized adaptive intervention sequences. It does not supply IBS efficacy, an IBS switching rule, or a validated IBS policy."
  Source.publicAttribution

senarathne2020Source : Source.AttributedSource
senarathne2020Source = Source.mkDOISource
  "Siththara Gedara J Senarathne; Antony M Overstall; James M McGree"
  "Bayesian adaptive N-of-1 trials for estimating population and individual treatment effects"
  "Statistics in Medicine 39(29):4499-4518" "2020"
  "10.1002/sim.8737"
  "https://doi.org/10.1002/sim.8737"
  Source.academicArticleSource
  "Methodological donor for adaptive within-person treatment allocation while estimating individual and population effects. Simulated/motivating examples do not validate an IBS likelihood model or treatment policy."
  Source.publicAttribution

duan2013Source : Source.AttributedSource
duan2013Source = Source.mkNoDOISource
  "Naihua Duan et al."
  "Single-patient (n-of-1) trials: a pragmatic clinical decision methodology for patient-centered comparative effectiveness research"
  "Journal of Clinical Epidemiology" "2013"
  "https://pubmed.ncbi.nlm.nih.gov/23849149/"
  Source.academicArticleSource
  "Methodological review supporting randomized crossover, washout and repeated individual treatment-effect estimation for chronic conditions; it does not guarantee feasibility for every IBS intervention or eliminate carryover."
  Source.publicAttribution

so2022Source : Source.AttributedSource
so2022Source = Source.mkDOISource
  "Daniel So; Chu K Yao; Zaid S Ardalan; Phoebe A Thwaites; Kourosh Kalantar-Zadeh; Peter R Gibson; Jane G Muir"
  "Supplementing Dietary Fibers With a Low FODMAP Diet in Irritable Bowel Syndrome: A Randomized Controlled Crossover Trial"
  "Clinical Gastroenterology and Hepatology 20(9):2112-2120.e7" "2022"
  "10.1016/j.cgh.2021.12.016"
  "https://doi.org/10.1016/j.cgh.2021.12.016"
  Source.academicArticleSource
  "Monash crossover evidence that fibre manipulations on a low-FODMAP background changed stool bulk/water/transit without materially changing symptom-response rates. Physiological normalization and symptom benefit are retained as separate outcomes."
  Source.publicAttribution

bodyBrain2026Source : Source.AttributedSource
bodyBrain2026Source = Source.mkNoDOISource
  "Monash University Department of Gastroenterology / Alfred Health"
  "Body and Brain study - investigating fibre for irritable bowel syndrome"
  "Monash University recruiting study page" "2026"
  "https://www.monash.edu/medicine/translational/clinical-trials-and-research-studies/gastroenterology/body-and-brain-study-investigating-fibre-for-irritable-bowel-syndrome"
  Source.institutionalSource
  "Recruiting protocol-level surface: repeated fructan-containing/control test drinks, breath sampling, gut and mental-health symptom tracking and food intake in adults with IBS. Recruitment/design information is not an efficacy or mechanism result."
  Source.publicAttribution

balsiger2026Source : Source.AttributedSource
balsiger2026Source = Source.mkDOISource
  "Lukas Michaja Balsiger et al."
  "Individualized Targeted Exclusion Diet Based on Confocal Laser Endomicroscopy Does Not Improve Irritable Bowel Syndrome Symptoms: A Randomized Controlled Crossover Trial"
  "Gastroenterology" "2026"
  "10.1053/j.gastro.2026.08.026"
  "https://doi.org/10.1053/j.gastro.2026.08.026"
  Source.academicArticleSource
  "Double-blind controlled crossover evidence that CLE-targeted exclusion did not outperform sham exclusion and acute mucosal alterations were also seen in healthy controls. This is a negative validation result for that targeting signal, not proof that all food-mediated IBS mechanisms are absent."
  Source.publicAttribution

garciaCedillo2026Source : Source.AttributedSource
garciaCedillo2026Source = Source.mkDOISource
  "Maria Fernanda Garcia-Cedillo et al."
  "Effects of a Personalised FODMAP Diet Versus NICE Dietary Advice on Symptom Control in Patients With Irritable Bowel Syndrome: Randomised Clinical Trial"
  "Alimentary Pharmacology and Therapeutics 63(11):1529-1536" "2026"
  "10.1111/apt.70601"
  "https://doi.org/10.1111/apt.70601"
  Source.academicArticleSource
  "External randomized evidence for a less-restrictive personalized FODMAP strategy with no significant between-group difference from NICE advice in the represented trial. It informs transport and burden questions, not superiority of personalization."
  Source.publicAttribution

data TrialDesignKind : Set where
  smartSequentialRandomization : TrialDesignKind
  randomizedCrossover : TrialDesignKind
  adaptiveNOf1 : TrialDesignKind
  nutrientPerturbationCrossover : TrialDesignKind
  protocolOnlyRepeatedChallenge : TrialDesignKind
  negativeTargetingValidation : TrialDesignKind
  parallelPersonalizationTrial : TrialDesignKind

record TrialDesignDonor : Set where
  constructor trial-design-donor
  field
    source : Source.AttributedSource
    designKind : TrialDesignKind
    donorRole : String
    pays : String
    doesNotPay : String
open TrialDesignDonor public

canonicalIBSTrialDesignDonorAtlas : List TrialDesignDonor
canonicalIBSTrialDesignDonorAtlas =
  trial-design-donor collins2007Source smartSequentialRandomization
    "prospective multi-stage randomization"
    "design template for learning treatment sequences conditional on intermediate response"
    "IBS efficacy, numeric switching threshold, or participant mechanism" ∷
  trial-design-donor senarathne2020Source adaptiveNOf1
    "Bayesian adaptive repeated within-person allocation"
    "design machinery for jointly improving individual treatment choice and parameter information"
    "validated IBS posterior, prior, likelihood, or clinical decision threshold" ∷
  trial-design-donor duan2013Source randomizedCrossover
    "patient-centred N-of-1 comparative effectiveness"
    "randomization/crossover/washout and repeated symptom measurement obligations"
    "automatic suitability where treatment carryover, delayed onset or irreversible change dominates" ∷
  trial-design-donor so2022Source nutrientPerturbationCrossover
    "Monash fibre/FODMAP physiological perturbation"
    "within-person controlled diet periods with symptom and physiological outcomes"
    "equivalence of physiological and symptom response" ∷
  trial-design-donor bodyBrain2026Source protocolOnlyRepeatedChallenge
    "Monash current repeated fructan/control challenge protocol"
    "prospective design target coupling breath, gut, mental-health and dietary observations"
    "completed efficacy, causal mediation, or validated fructan-sensitive subtype" ∷
  trial-design-donor balsiger2026Source negativeTargetingValidation
    "falsifier for a candidate food-targeting biomarker"
    "controlled evidence that one plausible targeting signal failed sham-controlled validation"
    "universal absence of food sensitivity or mucosal mechanisms" ∷
  trial-design-donor garciaCedillo2026Source parallelPersonalizationTrial
    "external less-restrictive personalization comparison"
    "transport evidence that selective restriction can be trialled against conventional advice"
    "superiority, Monash provenance, or a validated adaptive policy" ∷ []

data SMARTDesignProvesIBSEfficacyPermission : Set where
smartDesignDoesNotProveIBSEfficacy : SMARTDesignProvesIBSEfficacyPermission → ⊥
smartDesignDoesNotProveIBSEfficacy ()

data NOf1ResultAutomaticallyGeneralizesPermission : Set where
nOf1DoesNotAutomaticallyGeneralize : NOf1ResultAutomaticallyGeneralizesPermission → ⊥
nOf1DoesNotAutomaticallyGeneralize ()

data CLEReactionIsValidatedFoodTargetPermission : Set where
cleReactionDoesNotValidateFoodTarget : CLEReactionIsValidatedFoodTargetPermission → ⊥
cleReactionDoesNotValidateFoodTarget ()

data RecruitingProtocolCreatesResultPermission : Set where
recruitingProtocolDoesNotCreateResult : RecruitingProtocolCreatesResultPermission → ⊥
recruitingProtocolDoesNotCreateResult ()

record TrialDesignDonorBoundary : Set where
  constructor trial-design-donor-boundary
  field
    methodologyAndIBSEvidenceSeparated : Bool
    prospectiveSwitchingRuleRequired : Bool
    washoutCarryoverMustBeAudited : Bool
    negativeValidationCanDowngradeTargetingSignal : Bool
    protocolOnlyEvidenceMarkedProtocolOnly : Bool
    noNumericPolicyInvented : Bool

canonicalTrialDesignDonorBoundary : TrialDesignDonorBoundary
canonicalTrialDesignDonorBoundary = trial-design-donor-boundary true true true true true true

record TrialDesignParetoNode : Set where
  constructor trial-design-pareto-node
  field
    label : String
    route : Snowball.DiscoveryRoute
    paidReference : String
    residual : String
    nextAcquisition : String
    attributionBoundary : String
open TrialDesignParetoNode public

canonicalIBSTrialDesignParetoFrontier : List TrialDesignParetoNode
canonicalIBSTrialDesignParetoFrontier =
  trial-design-pareto-node
    "SMART IBS sequence trial" Snowball.experimentalDesign
    "Collins/Murphy/Strecher 2007 supplies design structure only"
    "IBS-specific stages, response definitions and ethical switching constraints remain unvalidated"
    "prospectively define stage-1 choices, nonresponse/partial-response states, stage-2 rerandomization and patient-centred distal outcome"
    "SMART methodology is not IBS efficacy" ∷
  trial-design-pareto-node
    "adaptive N-of-1 IBS probe" Snowball.experimentalDesign
    "Senarathne/Overstall/McGree 2020 plus Duan et al. 2013"
    "IBS actions differ in onset, washout, carryover, burden and reversibility"
    "start with short/reversible challenge-rescue actions and explicit carryover model before broader treatment adaptation"
    "within-person optimality does not automatically generalize" ∷
  trial-design-pareto-node
    "Monash Body-and-Brain fructan challenge acquisition" Snowball.externalKnowledgeComparison
    "current Monash recruiting protocol"
    "results not yet available on the cited study page"
    "when results appear, ingest breath/symptom/mental-health timing without upgrading protocol claims retroactively"
    "recruitment page is protocol provenance only" ∷
  trial-design-pareto-node
    "targeting-signal falsification lane" Snowball.externalKnowledgeComparison
    "Balsiger et al. 2026 DOI 10.1053/j.gastro.2026.08.026"
    "need comparable sham-controlled validation for other proposed targeting biomarkers"
    "require target-selection biomarkers to beat sham/usual-selection in prospective controlled designs"
    "mechanistic plausibility is not sufficient targeting validity" ∷ []
