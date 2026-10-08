module DASHI.Biology.QuailEggAllergySafetyBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Snowball
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Design

delgadoPrada2025Source : Source.AttributedSource
delgadoPrada2025Source = Source.mkDOISource
  "Ana Delgado-Prada; Maria Jose Martinez-Martinez; Enrique Burches; Angel Sastre-Sastre; Fernando Pineda De La Losa; Celia Morales-Rubio"
  "Quail egg allergy with tolerance to chicken eggs: A case report"
  "Journal of Allergy and Clinical Immunology: Global 4(3):100486" "2025"
  "10.1016/j.jacig.2025.100486" "https://doi.org/10.1016/j.jacig.2025.100486"
  Source.academicArticleSource
  "Pays a single adult case showing clinically significant quail-egg allergy despite chicken-egg tolerance. It establishes possibility, not prevalence or a population-level risk estimate."
  Source.publicAttribution

yamashita2024Source : Source.AttributedSource
yamashita2024Source = Source.mkDOISource
  "Kosei Yamashita; Yuki Okada; Aiko Honda; Chihiro Kunigami; Mayu Maeda; Toshinori Nakamura; Taro Kamiya; Takanori Imai"
  "Clinical Features of Quail Egg Ingestion in Patients with Acquired Tolerance to Hen Eggs: A Case Series Study"
  "International Archives of Allergy and Immunology 185(2):152-157" "2024"
  "10.1159/000534825" "https://doi.org/10.1159/000534825"
  Source.academicArticleSource
  "Pays a prospective pediatric case-series oral-food-challenge result: 59 participants who completed ingestion of three boiled quail eggs had no allergic reaction. This does not guarantee tolerance in all hen-egg-tolerant people and does not negate rare quail-specific allergy."
  Source.publicAttribution

data SafetyEvidenceKind : Set where
  individualCaseReport : SafetyEvidenceKind
  prospectiveOralChallengeCaseSeries : SafetyEvidenceKind

record QuailEggAllergyEvidenceReceipt : Set where
  constructor quail-egg-allergy-evidence-receipt
  field source : Source.AttributedSource
        evidenceKind : SafetyEvidenceKind
        henEggTolerancePresent : Bool
        quailEggReactionObserved : Bool
        populationGuaranteePaid : Bool
        boundary : String

delgadoPrada2025Receipt : QuailEggAllergyEvidenceReceipt
delgadoPrada2025Receipt = quail-egg-allergy-evidence-receipt
  delgadoPrada2025Source individualCaseReport true true false
  "Rare counterexample surface: hen/chicken-egg tolerance cannot definitionally guarantee quail-egg tolerance. A case report does not quantify prevalence."

yamashita2024Receipt : QuailEggAllergyEvidenceReceipt
yamashita2024Receipt = quail-egg-allergy-evidence-receipt
  yamashita2024Source prospectiveOralChallengeCaseSeries true false false
  "Bounded reassuring oral-challenge evidence in a pediatric acquired-hen-egg-tolerance cohort; study scope does not establish universal quail tolerance."

data HenEggToleranceImpliesQuailEggTolerancePermission : Set where
henToleranceDoesNotGuaranteeQuailTolerance :
  HenEggToleranceImpliesQuailEggTolerancePermission → ⊥
henToleranceDoesNotGuaranteeQuailTolerance ()

data OneCaseDeterminesPopulationRiskPermission : Set where
oneCaseDoesNotDeterminePopulationRisk : OneCaseDeterminesPopulationRiskPermission → ⊥
oneCaseDoesNotDeterminePopulationRisk ()

data OneCaseSeriesDeterminesUniversalSafetyPermission : Set where
caseSeriesDoesNotDetermineUniversalSafety : OneCaseSeriesDeterminesUniversalSafetyPermission → ⊥
caseSeriesDoesNotDetermineUniversalSafety ()

record QuailEggInterventionSafetyRequirement : Set where
  constructor quail-egg-intervention-safety-requirement
  field discoveryRoute : Snowball.DiscoveryRoute
        sourcePopulationSlot : Design.ExperimentalDesignSlot
        baselineMeasurementSlot : Design.ExperimentalDesignSlot
        endpointMeasurementSlot : Design.ExperimentalDesignSlot
        nuisanceControlSlot : Design.ExperimentalDesignSlot
        practicalSignificanceSlot : Design.ExperimentalDesignSlot
        quailSpecificAllergyHistoryRequired : Bool
        quailSpecificAllergyHistoryRequiredIsTrue : quailSpecificAllergyHistoryRequired ≡ true
        adverseEventSurveillanceRequired : Bool
        adverseEventSurveillanceRequiredIsTrue : adverseEventSurveillanceRequired ≡ true
        henEggToleranceCannotSubstituteForQuailAssessment : Bool
        henEggToleranceCannotSubstituteForQuailAssessmentIsTrue :
          henEggToleranceCannotSubstituteForQuailAssessment ≡ true
        requirementReference : String

canonicalQuailEggInterventionSafetyRequirement : QuailEggInterventionSafetyRequirement
canonicalQuailEggInterventionSafetyRequirement = quail-egg-intervention-safety-requirement
  Snowball.experimentalDesign
  Design.sourcePopulationSlot Design.baselineMeasurementSlot Design.endpointMeasurementSlot
  Design.nuisanceControlSlot Design.practicalSignificanceSlot
  true refl true refl true refl
  "Any quail-egg intervention must retain quail-specific allergy history/risk, adverse-event monitoring and stopping criteria. Hen-egg tolerance is informative context but cannot be used as a proof of quail-egg safety."

record QuailEggAllergySafetyBoundary : Set where
  constructor quail-egg-allergy-safety-boundary
  field rareDiscordantAllergyPossibilityPaid : Bool
        rareDiscordantAllergyPossibilityPaidIsTrue : rareDiscordantAllergyPossibilityPaid ≡ true
        boundedReassuringChallengeEvidencePaid : Bool
        boundedReassuringChallengeEvidencePaidIsTrue : boundedReassuringChallengeEvidencePaid ≡ true
        henEggToleranceGuaranteesQuailTolerance : Bool
        henEggToleranceGuaranteesQuailToleranceIsFalse : henEggToleranceGuaranteesQuailTolerance ≡ false
        prevalenceEstablishedByCaseReport : Bool
        prevalenceEstablishedByCaseReportIsFalse : prevalenceEstablishedByCaseReport ≡ false
        universalSafetyEstablishedByCaseSeries : Bool
        universalSafetyEstablishedByCaseSeriesIsFalse : universalSafetyEstablishedByCaseSeries ≡ false
        safetyMustRemainInInterventionDesign : Bool
        safetyMustRemainInInterventionDesignIsTrue : safetyMustRemainInInterventionDesign ≡ true

canonicalQuailEggAllergySafetyBoundary : QuailEggAllergySafetyBoundary
canonicalQuailEggAllergySafetyBoundary = quail-egg-allergy-safety-boundary
  true refl true refl false refl false refl false refl true refl
