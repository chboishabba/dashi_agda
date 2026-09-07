module DASHI.Biology.Agriculture.BNFClimateCountryLESCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Biology.CarbonClimateEcologicalDependencyBidiExact as ClimateDependency
import DASHI.Biology.ClimateCarryingCapacityDeepTimeCrossPollinationExact as ClimateContext
import DASHI.Biology.Agriculture.HungriaEconomicEmissionModel2023Exact as Model2023
import DASHI.Biology.Agriculture.BNFEconomicValidationCrossPollinationExact as Econ
import DASHI.Biology.Agriculture.HungriaSourceAttributionPromotionBoundaryExact as Attribution
import DASHI.Cognition.PNF.SensibLawMaboTwoLegalOrderFibreExact as TwoOrder
import DASHI.Cognition.PNF.SensibLawMaboCrownRecognitionProjectionNonFactorabilityExact as Crown
import DASHI.Cognition.PNF.SensibLawIndigenousCarbonValueProjectionNonFactorabilityExact as CarbonValue

------------------------------------------------------------------------
-- BNF <-> CLIMATE <-> COUNTRY / MABO <-> LES CROSS-POLLINATION
--
-- This is a DASHI theorem-pattern owner.  It does NOT attribute the combined
-- architecture to Hungria, Telles, Nogueira, Mabo litigants/judges, Indigenous
-- communities, LES authors, Embrapa, CONAB, or climate-science authors.
--
-- The reused repository boundaries are:
--
--   * climate/ecology: changed carbon or climate observations selectively
--     reopen only proof-bearing dependents;
--   * Mabo/Country: Crown/admin recognition is not an exhaustive observer for
--     antecedent Country/community authority;
--   * carbon value: market/admin carbon coordinates do not exhaust ecological,
--     cultural or stewardship value;
--   * LES: runtime simulation/calibration/optimisation remains distinct from
--     DASHI semantic admission/promotion authority.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Selective reopening for the BNF climate/economic chain.
------------------------------------------------------------------------

data BNFClimateArtifact : Set where
  nitrogenaseMechanismCertificate
  soybeanBNFFieldCertificate
  fertilizerCounterfactualCertificate
  fertilizerPriceCertificate
  avoidedCostCertificate
  fertilizerEmissionFactorCertificate
  avoidedEmissionCertificate
  atmosphericForcingInterpretationCertificate
  localClimateHydrologyCertificate
  soybeanYieldResponseCertificate
  farmUnitEconomicsCertificate
  countryAuthorityCertificate
  communityConsentCertificate
  unrelatedMolecularIdentityCertificate
  : BNFClimateArtifact

data Depends : BNFClimateArtifact → BNFClimateArtifact → Set where
  fieldToCounterfactual :
    Depends soybeanBNFFieldCertificate fertilizerCounterfactualCertificate
  counterfactualToCost :
    Depends fertilizerCounterfactualCertificate avoidedCostCertificate
  priceToCost :
    Depends fertilizerPriceCertificate avoidedCostCertificate
  counterfactualToAvoidedEmission :
    Depends fertilizerCounterfactualCertificate avoidedEmissionCertificate
  emissionFactorToAvoidedEmission :
    Depends fertilizerEmissionFactorCertificate avoidedEmissionCertificate
  avoidedEmissionToForcingInterpretation :
    Depends avoidedEmissionCertificate atmosphericForcingInterpretationCertificate
  localClimateToYield :
    Depends localClimateHydrologyCertificate soybeanYieldResponseCertificate
  yieldToUnitEconomics :
    Depends soybeanYieldResponseCertificate farmUnitEconomicsCertificate
  costToUnitEconomics :
    Depends avoidedCostCertificate farmUnitEconomicsCertificate

ureaPriceReopensFarmEconomics :
  Dependency.ReopeningObligation Depends fertilizerPriceCertificate farmUnitEconomicsCertificate
ureaPriceReopensFarmEconomics =
  Dependency.obligationsCompose
    (Dependency.oneEdgeCreatesReopeningObligation priceToCost)
    (Dependency.oneEdgeCreatesReopeningObligation costToUnitEconomics)

emissionFactorReopensClimateInterpretation :
  Dependency.ReopeningObligation
    Depends fertilizerEmissionFactorCertificate atmosphericForcingInterpretationCertificate
emissionFactorReopensClimateInterpretation =
  Dependency.obligationsCompose
    (Dependency.oneEdgeCreatesReopeningObligation emissionFactorToAvoidedEmission)
    (Dependency.oneEdgeCreatesReopeningObligation avoidedEmissionToForcingInterpretation)

climateHydrologyReopensFarmEconomics :
  Dependency.ReopeningObligation Depends localClimateHydrologyCertificate farmUnitEconomicsCertificate
climateHydrologyReopensFarmEconomics =
  Dependency.obligationsCompose
    (Dependency.oneEdgeCreatesReopeningObligation localClimateToYield)
    (Dependency.oneEdgeCreatesReopeningObligation yieldToUnitEconomics)

------------------------------------------------------------------------
-- The absence of an edge is deliberate: changing a fertilizer price or climate
-- scenario does not rewrite the nitrogenase stoichiometry or source authorship.
------------------------------------------------------------------------

data UreaPriceChangeImpliesNitrogenaseMechanismRevisionPermission : Set where

data ClimateScenarioImpliesSourceAuthorshipRevisionPermission : Set where

data EmissionFactorRevisionImpliesBiologicalEfficacyRevisionPermission : Set where

ureaPriceChangeDoesNotAutoReviseNitrogenaseMechanism :
  UreaPriceChangeImpliesNitrogenaseMechanismRevisionPermission → ⊥
ureaPriceChangeDoesNotAutoReviseNitrogenaseMechanism ()

climateScenarioDoesNotAutoReviseSourceAuthorship :
  ClimateScenarioImpliesSourceAuthorshipRevisionPermission → ⊥
climateScenarioDoesNotAutoReviseSourceAuthorship ()

emissionFactorRevisionDoesNotAutoReviseBiologicalEfficacy :
  EmissionFactorRevisionImpliesBiologicalEfficacyRevisionPermission → ⊥
emissionFactorRevisionDoesNotAutoReviseBiologicalEfficacy ()

------------------------------------------------------------------------
-- 2. Climate accounting is not ecological totality.
------------------------------------------------------------------------

record BNFClimateBenefitVector : Set₁ where
  constructor bnfClimateBenefitVector
  field
    AvoidedManufacturingEmission : Set
    AvoidedTransportEmission : Set
    AvoidedFieldEmission : Set
    SoilNitrogenState : Set
    HydrologyState : Set
    YieldResponse : Set
    BiodiversityResponse : Set
    HabitatResponse : Set
    FarmerEconomicResponse : Set

open BNFClimateBenefitVector public

data AvoidedCO2eImpliesCompleteEcologicalBenefitPermission : Set where

data AvoidedCO2eImpliesStableCarryingCapacityPermission : Set where

data NationalEmissionBenefitImpliesLocalYieldBenefitPermission : Set where

avoidedCO2eDoesNotAutoPromoteToCompleteEcologicalBenefit :
  AvoidedCO2eImpliesCompleteEcologicalBenefitPermission → ⊥
avoidedCO2eDoesNotAutoPromoteToCompleteEcologicalBenefit ()

avoidedCO2eDoesNotAutoPromoteToStableCarryingCapacity :
  AvoidedCO2eImpliesStableCarryingCapacityPermission → ⊥
avoidedCO2eDoesNotAutoPromoteToStableCarryingCapacity ()

nationalEmissionBenefitDoesNotAutoPromoteToLocalYieldBenefit :
  NationalEmissionBenefitImpliesLocalYieldBenefitPermission → ⊥
nationalEmissionBenefitDoesNotAutoPromoteToLocalYieldBenefit ()

climateCarryingCapacityBoundary : ClimateContext.ClimateCarryingCapacityDeepTimeBoundary
climateCarryingCapacityBoundary = ClimateContext.canonicalClimateCarryingCapacityDeepTimeBoundary

carbonClimateSelectiveReopeningBoundary :
  ClimateDependency.CarbonClimateEcologicalDependencyBoundary
carbonClimateSelectiveReopeningBoundary =
  ClimateDependency.canonicalCarbonClimateEcologicalDependencyBoundary

------------------------------------------------------------------------
-- 3. Mabo/Country cross-pollination.
--
-- Carbon, economic and simulation observers are useful but cannot be promoted
-- into Country/community authority.  This mirrors the repo's existing theorem
-- that Crown recognition does not factor Indigenous authority.
------------------------------------------------------------------------

data CountryPlanningObserver : Set where
  sameCarbonAndEconomicSurface : CountryPlanningObserver

data CountryAuthorityOutcome : Set where
  authorityConstraintLow
  authorityConstraintHigh
  : CountryAuthorityOutcome

data SituatedCountryPlanningState : Set where
  sameMetricsDifferentAuthorityLow
  sameMetricsDifferentAuthorityHigh
  : SituatedCountryPlanningState

countryPlanningObserver : SituatedCountryPlanningState → CountryPlanningObserver
countryPlanningObserver sameMetricsDifferentAuthorityLow = sameCarbonAndEconomicSurface
countryPlanningObserver sameMetricsDifferentAuthorityHigh = sameCarbonAndEconomicSurface

countryAuthorityOutcome : SituatedCountryPlanningState → CountryAuthorityOutcome
countryAuthorityOutcome sameMetricsDifferentAuthorityLow = authorityConstraintLow
countryAuthorityOutcome sameMetricsDifferentAuthorityHigh = authorityConstraintHigh

countryAuthorityOutcomesDiffer :
  countryAuthorityOutcome sameMetricsDifferentAuthorityLow ≡
  countryAuthorityOutcome sameMetricsDifferentAuthorityHigh → ⊥
countryAuthorityOutcomesDiffer ()

record CountryPlanningBoundary : Set where
  constructor countryPlanningBoundary
  field
    carbonBenefitCreatesCountryAuthority : Bool
    carbonBenefitCreatesCountryAuthorityIsFalse :
      carbonBenefitCreatesCountryAuthority ≡ false
    farmProfitCreatesCommunityConsent : Bool
    farmProfitCreatesCommunityConsentIsFalse :
      farmProfitCreatesCommunityConsent ≡ false
    simulatorOutputDeterminesCountryObligation : Bool
    simulatorOutputDeterminesCountryObligationIsFalse :
      simulatorOutputDeterminesCountryObligation ≡ false
    crownRecognitionStillDoesNotCreateIndigenousOrder : Bool
    crownRecognitionStillDoesNotCreateIndigenousOrderIsTrue :
      crownRecognitionStillDoesNotCreateIndigenousOrder ≡ true
    countryAuthorityMustRemainIndependentCoordinate : Bool
    countryAuthorityMustRemainIndependentCoordinateIsTrue :
      countryAuthorityMustRemainIndependentCoordinate ≡ true

canonicalCountryPlanningBoundary : CountryPlanningBoundary
canonicalCountryPlanningBoundary =
  countryPlanningBoundary
    false refl
    false refl
    false refl
    true refl
    true refl

crownRecognitionStillDoesNotFactorAuthority :
  ∀ {Recharted : Set} →
  (rechart : Crown.CrownRecognitionObservation → Recharted) →
  DASHI.Core.IntersectionalNonFactorability.FactorsThrough
    (λ state → rechart (Crown.crownRecognitionObserver state))
    Crown.indigenousAuthorityOutcome → ⊥
crownRecognitionStillDoesNotFactorAuthority =
  Crown.crownRecognitionRechartingStillCannotRecoverIndigenousAuthority

indigenousOrderNotCreatedByExternalRecognition :
  TwoOrder.externalRecognitionCreatesOrder TwoOrder.indigenousOrderFibre ≡ false
indigenousOrderNotCreatedByExternalRecognition = refl

carbonMarketPriceStillNotStewardshipValue :
  CarbonValue.CarbonMarketPriceEqualsSocialCarbonValue → ⊥
carbonMarketPriceStillNotStewardshipValue = CarbonValue.marketPriceDoesNotEqualSocialValue

------------------------------------------------------------------------
-- 4. LES planning-contract interface.
--
-- Prior LES planning architecture assigns semantic contracts and promotion
-- gates to dashi_agda, while LES owns GIS state, model execution, calibration,
-- optimisation and evidence serialization.  We preserve that direction here.
------------------------------------------------------------------------

data LESRuntimeResponsibility : Set where
  gisStateConstruction
  weatherClimateForcingExecution
  soilHydrologyExecution
  plantGrowthExecution
  nutrientFlowExecution
  interventionSimulation
  calibrationExecution
  optimisationExecution
  evidenceSerialization
  : LESRuntimeResponsibility

data DASHISemanticResponsibility : Set where
  variableMeaningContract
  invariantMeaningContract
  sourceAuthorityGate
  sameObjectPromotionGate
  attributionGate
  countryAuthorityNoncollapseGate
  : DASHISemanticResponsibility

record LESPlanningReceiptSurface : Set₁ where
  constructor lesPlanningReceiptSurface
  field
    Scenario : Set
    Artifact : Set
    simulatedScenario : Scenario
    hashedOrVersionedArtifact : Artifact
    runtimeReference : String
    calibrationReference : String
    evidenceReference : String
    semanticContractReference : String

open LESPlanningReceiptSurface public

data LESOutputImpliesDASHISemanticValidityPermission : Set where

data LESCalibrationImpliesSourceTruthPermission : Set where

data LESOptimisationImpliesPoliticalAuthorityPermission : Set where

data DASHIContractImpliesLESNumericalCalibrationPermission : Set where

lesOutputDoesNotAutoPromoteToDASHISemanticValidity :
  LESOutputImpliesDASHISemanticValidityPermission → ⊥
lesOutputDoesNotAutoPromoteToDASHISemanticValidity ()

lesCalibrationDoesNotAutoPromoteToSourceTruth :
  LESCalibrationImpliesSourceTruthPermission → ⊥
lesCalibrationDoesNotAutoPromoteToSourceTruth ()

lesOptimisationDoesNotAutoPromoteToPoliticalAuthority :
  LESOptimisationImpliesPoliticalAuthorityPermission → ⊥
lesOptimisationDoesNotAutoPromoteToPoliticalAuthority ()

dashiContractDoesNotAutoPromoteToLESCalibration :
  DASHIContractImpliesLESNumericalCalibrationPermission → ⊥
dashiContractDoesNotAutoPromoteToLESCalibration ()

------------------------------------------------------------------------
-- 5. Combined intervention receipt.
------------------------------------------------------------------------

record QualifiedBNFInterventionReceipt : Set₁ where
  constructor qualifiedBNFInterventionReceipt
  field
    BiologicalReceipt : Set
    EconomicReceipt : Set
    ClimateAccountingReceipt : Set
    LESExecutionReceipt : Set
    SourceAttributionReceipt : Set
    CountryAuthorityReceipt : Set
    biologicalReceipt : BiologicalReceipt
    economicReceipt : EconomicReceipt
    climateAccountingReceipt : ClimateAccountingReceipt
    lesExecutionReceipt : LESExecutionReceipt
    sourceAttributionReceipt : SourceAttributionReceipt
    countryAuthorityReceipt : CountryAuthorityReceipt

open QualifiedBNFInterventionReceipt public

data BiologyEconomicsClimateLESWithoutAuthorityImpliesQualifiedUsePermission : Set where

data CountryAuthorityWithoutEmpiricalAdequacyImpliesModelValidityPermission : Set where

technicalBundleDoesNotAutoPromoteToQualifiedUse :
  BiologyEconomicsClimateLESWithoutAuthorityImpliesQualifiedUsePermission → ⊥
technicalBundleDoesNotAutoPromoteToQualifiedUse ()

countryAuthorityDoesNotAutoPromoteToModelValidity :
  CountryAuthorityWithoutEmpiricalAdequacyImpliesModelValidityPermission → ⊥
countryAuthorityDoesNotAutoPromoteToModelValidity ()

------------------------------------------------------------------------
-- Existing source/version facts remain separate.
------------------------------------------------------------------------

paper2019_2020Mitigation = Model2023.mitigationIs183MillionMg
nationalSavingsDoesNotMeanTerminalFarmerBenefit =
  Econ.nationalAvoidedCostDoesNotAutoPromoteToTerminalFarmerBenefit
quoteDoesNotSupplyCalculationReplay =
  Attribution.speakerQuoteDoesNotSupplyCalculationReplay
