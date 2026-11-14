module DASHI.Biology.IBSMonashLongHorizonAdaptiveExact where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.IBSMonashAdaptiveSequencingExact as Adaptive
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Snowball

silva2025LongTermSource : Source.AttributedSource
silva2025LongTermSource = Source.mkDOISource
  "Hannah Silva; Judi Porter; Jacqueline Barrett; Peter R Gibson; Mayur Garg"
  "Dietary Intake, Symptom Control and Quality of Life After Dietitian-Delivered Education on a FODMAP Diet for Irritable Bowel Syndrome: A 7-Year Follow Up"
  "Neurogastroenterology and Motility 37(12):e70116" "2025"
  "10.1111/nmo.70116"
  "https://doi.org/10.1111/nmo.70116"
  Source.academicArticleSource
  "Monash-linked retrospective long-term follow-up after dietitian-led FODMAP education. Most participants were not on strict restriction at long follow-up; strict restriction was associated with lower food-related quality of life. This supports personalization/minimal-effective restriction as a burden-sensitive design consideration, not a causal mechanism theorem."
  Source.publicAttribution

silva2026SISource : Source.AttributedSource
silva2026SISource = Source.mkDOISource
  "Hannah Silva; Tenghao Zheng; Judi Porter; Jacqueline Barrett; Mayur Garg; Peter R Gibson"
  "The Associations of Sucrase-Isomaltase Hypomorphic Variants With Long-Term Outcomes and Dietary Intake in an Australian Irritable Bowel Syndrome Population Educated on the FODMAP Diet"
  "United European Gastroenterology Journal 14(1):e70173" "2026"
  "10.1002/ueg2.70173"
  "https://doi.org/10.1002/ueg2.70173"
  Source.academicArticleSource
  "In this retrospective cohort, single sucrase-isomaltase hypomorphic variants were common but were not associated with initial FODMAP response, long-term symptom control or current sucrose/starch intake. This is a negative stratification result, not evidence that SI variation is irrelevant in all contexts."
  Source.publicAttribution

anderson2025DigitalGDHSource : Source.AttributedSource
anderson2025DigitalGDHSource = Source.mkDOISource
  "Ellen J Anderson; Simone L Peters; Peter R Gibson; Emma P Halmos"
  "Comparison of Digitally Delivered Gut-Directed Hypnotherapy Program With an Active Control for Irritable Bowel Syndrome"
  "American Journal of Gastroenterology 120(2):440-448" "2025"
  "10.14309/ajg.0000000000002921"
  "https://doi.org/10.14309/ajg.0000000000002921"
  Source.academicArticleSource
  "Monash randomized controlled evidence on digital gut-directed hypnotherapy versus active control, adding delivery/accessibility evidence to the brain-gut intervention family. Digital delivery performance is not assumed identical to therapist-delivered hypnotherapy or to diet."
  Source.publicAttribution

data LongHorizonEvidenceRole : Set where
  longTermPersonalisationBurden : LongHorizonEvidenceRole
  negativeGeneticStratification : LongHorizonEvidenceRole
  digitalBrainGutDelivery : LongHorizonEvidenceRole

record LongHorizonEvidence : Set where
  constructor long-horizon-evidence
  field
    source : Source.AttributedSource
    role : LongHorizonEvidenceRole
    paidObservation : String
    promotionBlocked : String
open LongHorizonEvidence public

canonicalMonashLongHorizonAtlas : List LongHorizonEvidence
canonicalMonashLongHorizonAtlas =
  long-horizon-evidence silva2025LongTermSource longTermPersonalisationBurden
    "long-term symptom control can coexist with personalized/minimally restrictive diets; persistent strict restriction carries food-related QoL cost"
    "observational follow-up does not prove that personalization itself caused long-term control" ∷
  long-horizon-evidence silva2026SISource negativeGeneticStratification
    "single SI hypomorphic-variant carriage did not distinguish short- or long-term FODMAP outcome in the studied cohort"
    "null association in this cohort does not establish universal genetic irrelevance" ∷
  long-horizon-evidence anderson2025DigitalGDHSource digitalBrainGutDelivery
    "digital gut-directed hypnotherapy has randomized controlled outcome evidence against active control"
    "digital delivery is not assumed equivalent to therapist delivery or to a mechanistic CNS-only intervention" ∷ []

data SingleSIHypomorphPredictsFODMAPOutcomePermission : Set where
singleSIHypomorphDoesNotPredictFODMAPOutcome : SingleSIHypomorphPredictsFODMAPOutcomePermission → ⊥
singleSIHypomorphDoesNotPredictFODMAPOutcome ()

data MoreRestrictionAlwaysBetterPermission : Set where
moreRestrictionIsNotAlwaysBetter : MoreRestrictionAlwaysBetterPermission → ⊥
moreRestrictionIsNotAlwaysBetter ()

data DigitalGDHEqualsTherapistGDHPermission : Set where
digitalGDHDoesNotDefinitionallyEqualTherapistGDH : DigitalGDHEqualsTherapistGDHPermission → ⊥
digitalGDHDoesNotDefinitionallyEqualTherapistGDH ()

record BurdenSensitiveAdaptiveObjective : Set where
  constructor burden-sensitive-adaptive-objective
  field
    symptomBenefitRetained : Bool
    foodRelatedQoLRetained : Bool
    restrictionBurdenRetained : Bool
    accessDeliveryBurdenRetained : Bool
    informationValueRetained : Bool
    numericUtilityInvented : Bool
open BurdenSensitiveAdaptiveObjective public

canonicalBurdenSensitiveAdaptiveObjective : BurdenSensitiveAdaptiveObjective
canonicalBurdenSensitiveAdaptiveObjective = burden-sensitive-adaptive-objective true true true true true false

record LongHorizonParetoNode : Set where
  constructor long-horizon-pareto-node
  field
    label : String
    route : Snowball.DiscoveryRoute
    paidReference : String
    residual : String
    nextAcquisition : String
    authorityBoundary : String
open LongHorizonParetoNode public

canonicalMonashLongHorizonPareto : List LongHorizonParetoNode
canonicalMonashLongHorizonPareto =
  long-horizon-pareto-node
    "minimal-effective dietary restriction"
    Snowball.externalKnowledgeComparison
    "Silva 2025 DOI 10.1111/nmo.70116"
    "retrospective long-term follow-up cannot identify the optimal reintroduction policy"
    "prospective randomized personalization/reintroduction strategy with symptom, nutrition and food-related QoL outcomes"
    "less restriction is not automatically better if symptom control deteriorates; optimize jointly" ∷
  long-horizon-pareto-node
    "SI genotype negative-stratification replication"
    Snowball.externalKnowledgeComparison
    "Silva 2026 DOI 10.1002/ueg2.70173"
    "double-carriers were too few and cohort was retrospective"
    "larger prospective genotype-by-diet interaction study with enzyme activity/phenotype where feasible"
    "single-variant null result is not universal absence of SI effects" ∷
  long-horizon-pareto-node
    "digital versus therapist brain-gut delivery"
    Snowball.experimentalDesign
    "Anderson 2025 DOI 10.14309/ajg.0000000000002921 plus Peters 2016 DOI 10.1111/apt.13706"
    "delivery mode, therapist contact, adherence, expectancy and cost are partially entangled"
    "head-to-head pragmatic effectiveness/cost/access trial with common outcome and mechanism panel"
    "delivery convenience and mechanistic efficacy are distinct coordinates" ∷ []

record MonashLongHorizonBoundary : Set where
  constructor monash-long-horizon-boundary
  field
    adaptiveOwner : Adaptive.MonashAdaptiveBoundary
    nullSIResultRetained : Bool
    longTermBurdenRetained : Bool
    digitalDeliverySeparatedFromMechanism : Bool
    strictRestrictionIsUniversalGoal : Bool

canonicalMonashLongHorizonBoundary : MonashLongHorizonBoundary
canonicalMonashLongHorizonBoundary = monash-long-horizon-boundary
  Adaptive.canonicalMonashAdaptiveBoundary true true true false
