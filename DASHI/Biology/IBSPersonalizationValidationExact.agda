module DASHI.Biology.IBSPersonalizationValidationExact where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.IBSAdaptiveBeliefPolicyExact as Policy
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Snowball

------------------------------------------------------------------------
-- PERSONALIZATION IS A CLAIM THAT REQUIRES VALIDATION
--
-- A strategy may be individualized by food diary, microbiome model, imaging,
-- reintroduction history or another selector. The label itself does not prove
-- superiority, mechanism, calibration, transport, or clinical utility.
------------------------------------------------------------------------

garciaCedillo2026Source : Source.AttributedSource
garciaCedillo2026Source = Source.mkDOISource
  "Maria Fernanda Garcia-Cedillo; Maria Fernanda Huerta-de la Torre; Josealberto Sebastiano Arenas-Martinez; Enrique Coss-Adame"
  "Effects of a Personalised FODMAP Diet Versus the National Institute for Health and Care Excellence (NICE) Dietary Advice on Symptom Control in Patients With Irritable Bowel Syndrome: Randomised Clinical Trial"
  "Alimentary Pharmacology & Therapeutics 63(11):1529-1536" "2026"
  "10.1111/apt.70601"
  "https://doi.org/10.1111/apt.70601"
  Source.academicArticleSource
  "Randomized comparison of selective patient-specific FODMAP reduction with NICE dietary advice. The represented trial supports feasibility/comparable improvement but does not establish superiority of the personalized label or a validated mechanism selector."
  Source.publicAttribution

tunali2024Source : Source.AttributedSource
tunali2024Source = Source.mkDOISource
  "Varol Tunali et al."
  "A Multicenter Randomized Controlled Trial of Microbiome-Based Artificial Intelligence-Assisted Personalized Diet vs Low-FODMAP Diet: A Novel Approach for the Management of Irritable Bowel Syndrome"
  "American Journal of Gastroenterology 119(9):1901-1912" "2024"
  "10.14309/ajg.0000000000002862"
  "https://doi.org/10.14309/ajg.0000000000002862"
  Source.academicArticleSource
  "Multicenter randomized comparison of microbiome/AI-guided personalized diet and low-FODMAP diet. Both groups improved; the primary between-group IBS-SSS contrast was not significant. Multicenter randomization does not by itself externally validate the underlying selector algorithm."
  Source.publicAttribution

tunali2026Source : Source.AttributedSource
tunali2026Source = Source.mkDOISource
  "Varol Tunali et al."
  "Long-term microbiome and clinical effects of a microbiome-guided personalized diet versus low-FODMAP diet in irritable bowel syndrome: A 12-month follow-up randomized controlled trial"
  "Gut Microbes 18(1):2719125" "2026"
  "10.1080/19490976.2026.2719125"
  "https://doi.org/10.1080/19490976.2026.2719125"
  Source.academicArticleSource
  "Follow-up of the same randomized program reported a more durable symptom-response signal for the personalized-diet arm at 12 months and explicitly described the analysis as hypothesis-generating, with larger trials warranted. This linked follow-up is not independent external validation of the personalization algorithm."
  Source.publicAttribution

balsiger2026Source : Source.AttributedSource
balsiger2026Source = Source.mkDOISource
  "Lukas Michaja Balsiger et al."
  "Individualized Targeted Exclusion Diet Based on Confocal Laser Endomicroscopy Does Not Improve Irritable Bowel Syndrome Symptoms: A Randomized Controlled Crossover Trial"
  "Gastroenterology, online ahead of print" "2026"
  "10.1053/j.gastro.2026.08.026"
  "https://doi.org/10.1053/j.gastro.2026.08.026"
  Source.academicArticleSource
  "Double-blind controlled crossover evidence that CLE-targeted exclusion did not outperform sham exclusion and acute mucosal changes were also observed in healthy controls. This downgrades CLE as a validated targeting selector, not all food-mediated IBS hypotheses."
  Source.publicAttribution

silva2025Source : Source.AttributedSource
silva2025Source = Source.mkDOISource
  "Hannah Silva; Judi Porter; Jacqueline Barrett; Peter R Gibson; Mayur Garg"
  "Dietary Intake, Symptom Control and Quality of Life After Dietitian-Delivered Education on a FODMAP Diet for Irritable Bowel Syndrome: A 7-Year Follow Up"
  "Neurogastroenterology and Motility 37(12):e70116" "2025"
  "10.1111/nmo.70116"
  "https://doi.org/10.1111/nmo.70116"
  Source.academicArticleSource
  "Monash-linked retrospective long-term follow-up supporting burden-sensitive personalized/minimally restrictive practice. It does not identify the causal effect of personalization or validate a treatment-selection algorithm."
  Source.publicAttribution

data PersonalizationStrategyKind : Set where
  selectiveDiaryGuidedFODMAP : PersonalizationStrategyKind
  microbiomeAIGuidedDiet : PersonalizationStrategyKind
  biomarkerGuidedExclusion : PersonalizationStrategyKind
  dietitianReintroductionPersonalization : PersonalizationStrategyKind

data PersonalizationValidationStatus : Set where
  randomizedNoSuperiority : PersonalizationValidationStatus
  randomizedComparableImprovement : PersonalizationValidationStatus
  linkedLongTermDurabilitySignal : PersonalizationValidationStatus
  targetingSignalFailedSham : PersonalizationValidationStatus
  observationalLongTermBurdenEvidence : PersonalizationValidationStatus

record PersonalizationValidationEvidence : Set where
  constructor personalization-validation-evidence
  field
    source : Source.AttributedSource
    strategy : PersonalizationStrategyKind
    status : PersonalizationValidationStatus
    comparatorReference : String
    paidObservation : String
    selectorExternallyValidated : Bool
    clinicalUtilityValidated : Bool
    mechanismIdentified : Bool
    transportEstablished : Bool
open PersonalizationValidationEvidence public

canonicalIBSPersonalizationValidationAtlas : List PersonalizationValidationEvidence
canonicalIBSPersonalizationValidationAtlas =
  personalization-validation-evidence garciaCedillo2026Source selectiveDiaryGuidedFODMAP
    randomizedComparableImprovement
    "NICE dietary advice"
    "selective 50% reduction of patient-specific high-FODMAP foods was feasible and produced improvement, without represented evidence of superior primary clinical outcome"
    false false false false ∷
  personalization-validation-evidence tunali2024Source microbiomeAIGuidedDiet
    randomizedNoSuperiority
    "standard low-FODMAP diet"
    "both groups improved; primary between-group IBS-SSS contrast was not significant"
    false false false false ∷
  personalization-validation-evidence tunali2026Source microbiomeAIGuidedDiet
    linkedLongTermDurabilitySignal
    "12-month linked follow-up of low-FODMAP arm"
    "hypothesis-generating durability signal favoured the personalized-diet arm at 12 months"
    false false false false ∷
  personalization-validation-evidence balsiger2026Source biomarkerGuidedExclusion
    targetingSignalFailedSham
    "sham food exclusion after the same CLE procedure"
    "CLE-targeted exclusion did not outperform sham in the controlled crossover"
    false false false false ∷
  personalization-validation-evidence silva2025Source dietitianReintroductionPersonalization
    observationalLongTermBurdenEvidence
    "long-term observed dietary patterns after FODMAP education"
    "symptom control often coexisted with non-strict/personalized diets; persistent strict restriction carried lower food-related QoL"
    false false false false ∷ []

data PersonalizedLabelImpliesSuperiorOutcomePermission : Set where
personalizedLabelDoesNotImplySuperiorOutcome : PersonalizedLabelImpliesSuperiorOutcomePermission → ⊥
personalizedLabelDoesNotImplySuperiorOutcome ()

data MechanisticBiomarkerIsValidatedSelectorPermission : Set where
mechanisticBiomarkerDoesNotBecomeValidatedSelector : MechanisticBiomarkerIsValidatedSelectorPermission → ⊥
mechanisticBiomarkerDoesNotBecomeValidatedSelector ()

data InternalPersonalizationModelAutomaticallyTransportsPermission : Set where
internalPersonalizationModelDoesNotAutomaticallyTransport : InternalPersonalizationModelAutomaticallyTransportsPermission → ⊥
internalPersonalizationModelDoesNotAutomaticallyTransport ()

data LinkedFollowUpIsIndependentValidationPermission : Set where
linkedFollowUpDoesNotBecomeIndependentValidation : LinkedFollowUpIsIndependentValidationPermission → ⊥
linkedFollowUpDoesNotBecomeIndependentValidation ()

data NegativeSelectorTrialRefutesAllFoodMechanismsPermission : Set where
negativeSelectorDoesNotRefuteAllFoodMechanisms : NegativeSelectorTrialRefutesAllFoodMechanismsPermission → ⊥
negativeSelectorDoesNotRefuteAllFoodMechanisms ()

record PersonalizationValidationBoundary : Set where
  constructor personalization-validation-boundary
  field
    personalizationLabelNonPromoting : Bool
    prospectiveComparatorRequiredForUtility : Bool
    selectorNeedsCalibrationAndTransport : Bool
    linkedFollowUpKeptDistinctFromIndependentReplication : Bool
    negativeTargetingEvidenceCanDowngradeSelector : Bool
    negativeTargetingEvidenceRefutesWholeDomain : Bool
    policyOwner : Policy.AdaptivePolicyBoundary

canonicalPersonalizationValidationBoundary : PersonalizationValidationBoundary
canonicalPersonalizationValidationBoundary = personalization-validation-boundary
  true true true true true false Policy.canonicalAdaptivePolicyBoundary

record PersonalizationParetoNode : Set where
  constructor personalization-pareto-node
  field
    label : String
    route : Snowball.DiscoveryRoute
    paidReference : String
    residual : String
    nextAcquisition : String
    authorityBoundary : String
open PersonalizationParetoNode public

canonicalIBSPersonalizationParetoFrontier : List PersonalizationParetoNode
canonicalIBSPersonalizationParetoFrontier =
  personalization-pareto-node
    "guided-versus-usual clinical utility" Snowball.experimentalDesign
    "Garcia-Cedillo 2026 and Tunali 2024 provide randomized comparative outcomes"
    "personalization strategies have not established universal superiority or a common selector"
    "prospective policy trial with predeclared selector, comparator, calibration and patient-centred net-benefit outcomes"
    "the word personalized is not an efficacy endpoint" ∷
  personalization-pareto-node
    "locked selector transport" Snowball.externalKnowledgeComparison
    "Tunali 2024 multicenter microbiome-AI diet"
    "algorithm calibration/transport outside the development/program lineage remains open"
    "freeze selector and decision threshold before held-out geographic/laboratory replication"
    "multicenter data do not automatically equal independent algorithm validation" ∷
  personalization-pareto-node
    "long-term durability replication" Snowball.externalKnowledgeComparison
    "Tunali 2026 linked 12-month follow-up DOI 10.1080/19490976.2026.2719125"
    "follow-up is linked to the original program and explicitly hypothesis-generating"
    "independent adequately powered long-horizon trial using the locked selector"
    "durability signal is not independent validation" ∷
  personalization-pareto-node
    "targeting biomarker falsification benchmark" Snowball.externalKnowledgeComparison
    "Balsiger 2026 CLE sham-controlled crossover"
    "other plausible targeting biomarkers may fail once treatment selection is sham-controlled"
    "require guided-vs-sham/usual selection rather than mechanism-only association before policy admission"
    "negative CLE result downgrades CLE selector authority, not all food mechanisms" ∷
  personalization-pareto-node
    "minimal-effective restriction utility" Snowball.experimentalDesign
    "Silva 2025 long-horizon Monash burden evidence"
    "optimal reintroduction rule and nutritional/QoL tradeoff remain unvalidated"
    "randomized protocolized reintroduction/personalization versus usual dietetic care with symptom, nutrition and food-QoL co-outcomes"
    "observational long-term burden evidence does not establish causal policy superiority" ∷ []
