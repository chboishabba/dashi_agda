module DASHI.Governance.MedicalCannabisComparativeInstitutionalMeaningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.ComparativeInstitutionalMeaningExact as Comparative
import DASHI.Reasoning.SemanticEpistemicInterpretationExact as SemEpi
import DASHI.Governance.MedicalCannabisContaminantSemanticEpistemicExact as Cannabis

------------------------------------------------------------------------
-- CONDITIONAL COMPARATIVE INSTITUTIONAL FIXTURE
--
-- This is not an empirical claim that one institutional form has a measured
-- contamination rate relative to another.  It specifies what such a claim
-- would have to carry before `possibleStructuralCapitalistContribution` can be
-- promoted from semantic candidate to comparative structural interpretation.
------------------------------------------------------------------------

data ActualMarketState : Set where
  actualMarketFixture : ActualMarketState

data AlternativeProvisionState : Set where
  alternativeProvisionFixture : AlternativeProvisionState

actualWorld : Comparative.InstitutionalWorld
actualWorld = Comparative.institutionalWorld
  ActualMarketState
  actualMarketFixture
  actualRelation
  "synthetic actual medical-cannabis institutional world"
  "fixture only; requires empirical realization"
  where
    actualRelation : Comparative.InstitutionalCoordinate → Comparative.CoordinateRelation
    actualRelation Comparative.ownershipCoordinate = Comparative.intentionallyVaried
    actualRelation Comparative.profitIncentiveCoordinate = Comparative.intentionallyVaried
    actualRelation Comparative.externalityAllocationCoordinate = Comparative.intentionallyVaried
    actualRelation Comparative.regulatoryRuleCoordinate = Comparative.heldMatched
    actualRelation Comparative.enforcementCapacityCoordinate = Comparative.heldMatched
    actualRelation Comparative.informationTransparencyCoordinate = Comparative.unresolvedCoordinate
    actualRelation Comparative.patientVoiceCoordinate = Comparative.unresolvedCoordinate
    actualRelation Comparative.productionTechnologyCoordinate = Comparative.heldMatched
    actualRelation Comparative.productStandardCoordinate = Comparative.heldMatched
    actualRelation Comparative.populationCoordinate = Comparative.heldMatched
    actualRelation Comparative.timeCoordinate = Comparative.heldMatched

alternativeWorld : Comparative.InstitutionalWorld
alternativeWorld = Comparative.institutionalWorld
  AlternativeProvisionState
  alternativeProvisionFixture
  alternativeRelation
  "synthetic alternative medical-cannabis provisioning world"
  "fixture only; no empirical superiority asserted"
  where
    alternativeRelation : Comparative.InstitutionalCoordinate → Comparative.CoordinateRelation
    alternativeRelation Comparative.ownershipCoordinate = Comparative.intentionallyVaried
    alternativeRelation Comparative.profitIncentiveCoordinate = Comparative.intentionallyVaried
    alternativeRelation Comparative.externalityAllocationCoordinate = Comparative.intentionallyVaried
    alternativeRelation Comparative.regulatoryRuleCoordinate = Comparative.heldMatched
    alternativeRelation Comparative.enforcementCapacityCoordinate = Comparative.heldMatched
    alternativeRelation Comparative.informationTransparencyCoordinate = Comparative.unresolvedCoordinate
    alternativeRelation Comparative.patientVoiceCoordinate = Comparative.unresolvedCoordinate
    alternativeRelation Comparative.productionTechnologyCoordinate = Comparative.heldMatched
    alternativeRelation Comparative.productStandardCoordinate = Comparative.heldMatched
    alternativeRelation Comparative.populationCoordinate = Comparative.heldMatched
    alternativeRelation Comparative.timeCoordinate = Comparative.heldMatched

data Matched : Comparative.InstitutionalCoordinate → Set where
  matchedRegulatoryRule : Matched Comparative.regulatoryRuleCoordinate
  matchedEnforcement : Matched Comparative.enforcementCapacityCoordinate
  matchedProductionTechnology : Matched Comparative.productionTechnologyCoordinate
  matchedProductStandard : Matched Comparative.productStandardCoordinate
  matchedPopulation : Matched Comparative.populationCoordinate
  matchedTime : Matched Comparative.timeCoordinate

data Varied : Comparative.InstitutionalCoordinate → Set where
  variedOwnership : Varied Comparative.ownershipCoordinate
  variedProfitIncentive : Varied Comparative.profitIncentiveCoordinate
  variedExternalityAllocation : Varied Comparative.externalityAllocationCoordinate

noBoth :
  (coordinate : Comparative.InstitutionalCoordinate) →
  Matched coordinate →
  Varied coordinate →
  ⊥
noBoth Comparative.regulatoryRuleCoordinate matchedRegulatoryRule ()
noBoth Comparative.enforcementCapacityCoordinate matchedEnforcement ()
noBoth Comparative.productionTechnologyCoordinate matchedProductionTechnology ()
noBoth Comparative.productStandardCoordinate matchedProductStandard ()
noBoth Comparative.populationCoordinate matchedPopulation ()
noBoth Comparative.timeCoordinate matchedTime ()

contrast : Comparative.MatchedInstitutionalContrast actualWorld alternativeWorld
contrast = Comparative.matchedInstitutionalContrast
  Matched
  Varied
  noBoth
  "regulation/enforcement/technology/standard/population/time declared matched"
  "ownership/profit incentive/externality allocation declared varied"
  "synthetic contrast; empirical matching and residual-confounding audit still required"

------------------------------------------------------------------------
-- Outcome slot.  We deliberately do not construct a difference witness because
-- no empirical comparative outcome has been supplied here.
------------------------------------------------------------------------

data ContaminationOutcome : Set where
  contaminationOutcomeUnknown : ContaminationOutcome

record ComparativeCannabisEvidenceGap : Set where
  constructor comparativeCannabisEvidenceGap
  field
    actualOutcomeMeasurementMissing : String
    alternativeOutcomeMeasurementMissing : String
    recurrenceComparisonMissing : String
    matchingValidationMissing : String
    mediationEvidenceMissing : String
    transportAuditMissing : String

canonicalComparativeEvidenceGap : ComparativeCannabisEvidenceGap
canonicalComparativeEvidenceGap = comparativeCannabisEvidenceGap
  "need measured contamination/release-failure outcome in actual institutional setting"
  "need comparable outcome under alternative institutional setting or defensible quasi-experimental analogue"
  "need recurrence/time-series rather than one batch"
  "need validation that declared matched coordinates are actually comparable"
  "need evidence that ownership/incentive/externality coordinates mediate outcome difference"
  "need population/product/time transport audit"

------------------------------------------------------------------------
-- Semantic:epistemic bridge: the capitalism interpretation points to this
-- comparative design problem rather than directly to a conclusion.
------------------------------------------------------------------------

capitalismMeaningScale :
  Cannabis.meaningScale Cannabis.possibleStructuralCapitalistContribution
  ≡ SemEpi.politicalEconomyScale
capitalismMeaningScale = refl

record CapitalismComparativeBackprop : Set₁ where
  constructor capitalismComparativeBackprop
  field
    candidateMeaning : Cannabis.CannabisMeaning
    candidateIsStructuralCapitalism :
      candidateMeaning ≡ Cannabis.possibleStructuralCapitalistContribution
    requiredContrast : Comparative.MatchedInstitutionalContrast actualWorld alternativeWorld
    evidenceGap : ComparativeCannabisEvidenceGap
    comparisonReference : String
    noPromotionBeforeOutcomeComparisonReference : String

canonicalCapitalismComparativeBackprop : CapitalismComparativeBackprop
canonicalCapitalismComparativeBackprop = capitalismComparativeBackprop
  Cannabis.possibleStructuralCapitalistContribution
  refl
  contrast
  canonicalComparativeEvidenceGap
  "backprop political-economy interpretation into matched institutional comparison"
  "candidate remains unsupported until comparative outcome + mediation receipts exist"

record MedicalCannabisComparativeMeaningBoundary : Set where
  constructor medicalCannabisComparativeMeaningBoundary
  field
    capitalismCandidateAutomaticallySuppliesAlternativeWorld : Bool
    capitalismCandidateAutomaticallySuppliesAlternativeWorldIsFalse :
      capitalismCandidateAutomaticallySuppliesAlternativeWorld ≡ false
    syntheticContrastProvesCapitalistContribution : Bool
    syntheticContrastProvesCapitalistContributionIsFalse :
      syntheticContrastProvesCapitalistContribution ≡ false
    politicalEconomyMeaningCanBackpropToComparativeDesign : Bool
    politicalEconomyMeaningCanBackpropToComparativeDesignIsTrue :
      politicalEconomyMeaningCanBackpropToComparativeDesign ≡ true
    comparisonStillRequiresMeasuredOutcomeDifference : Bool
    comparisonStillRequiresMeasuredOutcomeDifferenceIsTrue :
      comparisonStillRequiresMeasuredOutcomeDifference ≡ true

canonicalMedicalCannabisComparativeMeaningBoundary :
  MedicalCannabisComparativeMeaningBoundary
canonicalMedicalCannabisComparativeMeaningBoundary =
  medicalCannabisComparativeMeaningBoundary
    false refl
    false refl
    true refl
    true refl
