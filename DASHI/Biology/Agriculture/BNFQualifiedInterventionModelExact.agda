module DASHI.Biology.Agriculture.BNFQualifiedInterventionModelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerIndexedModelFibreExact as Fibre
import DASHI.Core.CounterfactualModelContractExact as Counterfactual
import DASHI.Core.ModelAdequacyNonFactorabilityExact as Adequacy
import DASHI.Biology.Agriculture.BNFEconomicValidationCrossPollinationExact as Econ
import DASHI.Biology.Agriculture.BNFClimateCountryLESCrossPollinationExact as Cross
import DASHI.Biology.Agriculture.HungriaSourceAttributionPromotionBoundaryExact as Attribution
import DASHI.Cognition.PNF.SensibLawMaboTwoLegalOrderFibreExact as TwoOrder

------------------------------------------------------------------------
-- BNF QUALIFIED INTERVENTION MODEL
--
-- DASHI application of the generic consumer-indexed model fibre.
-- External science/economic/legal sources remain source owners only for their
-- bounded propositions.  The fibre architecture, counterfactual contract,
-- adequacy criterion and qualification theorem shapes are DASHI constructions.
------------------------------------------------------------------------

data BNFConsumerQuestion : Set where
  replayNationalAvoidedUreaExpenditure : BNFConsumerQuestion
  estimateNationalAvoidedCO2e : BNFConsumerQuestion
  predictLocalSoybeanYield : BNFConsumerQuestion
  estimateFarmNetBenefit : BNFConsumerQuestion
  predictEcologicalResponse : BNFConsumerQuestion
  decideLandscapeIntervention : BNFConsumerQuestion
  decideCountryAffectingIntervention : BNFConsumerQuestion


data BNFContext : Set where
  brazilNational : BNFContext
  stateRegional : BNFContext
  localFarm : BNFContext
  landscapeContext : BNFContext
  countryAffectingContext : BNFContext


data SpatialScale : Set where
  nationalScale : SpatialScale
  stateScale : SpatialScale
  farmScale : SpatialScale
  landscapeScale : SpatialScale

data TemporalWindow : Set where
  cropSeason : TemporalWindow
  multiSeason : TemporalWindow
  planningHorizon : TemporalWindow

data BNFIntervention : Set where
  inoculateBradyrhizobium : BNFIntervention
  noEffectiveBNF : BNFIntervention
  mineralNSubstitution : BNFIntervention


------------------------------------------------------------------------
-- Separate input carriers for each consumer family.
------------------------------------------------------------------------

record NationalEconomicReplayInputs : Set₁ where
  constructor national-economic-replay-inputs
  field
    State Season : Set
    Area Yield CropNDemand SecondaryN FertilizerRecovery UreaNContent
      UreaPrice BNFCounterfactual AggregationWeight : State → Season → Set
    sourceAndVersionReference : String

open NationalEconomicReplayInputs public

record FarmRealisationInputs : Set₁ where
  constructor farm-realisation-inputs
  field
    Farm Season : Set
    InoculantCost ApplicationCost FinancingCost YieldDifference SoybeanPrice
      FailureRisk ReplantCost LabourEquipmentCost RealizedFertilizerPurchase :
      Farm → Season → Set
    sourceAndCalibrationReference : String

open FarmRealisationInputs public

record ClimateAccountingFibre : Set₁ where
  constructor climate-accounting-fibre
  field
    Boundary Baseline Gas SourceProcess EmissionFactor TimeHorizon GWPConvention
      SpatialScope TemporalScope : Set
    boundary : Boundary
    baseline : Baseline
    gas : Gas
    sourceProcess : SourceProcess
    emissionFactor : EmissionFactor
    timeHorizon : TimeHorizon
    gwpConvention : GWPConvention
    spatialScope : SpatialScope
    temporalScope : TemporalScope
    manufactureIncluded transportIncluded fieldIncluded indirectIncluded : Bool
    accountingReference : String

open ClimateAccountingFibre public

record EcologicalLESState : Set₁ where
  constructor ecological-les-state
  field
    SoilN SoilC Moisture Hydrology Temperature Precipitation Habitat Biodiversity
      Disturbance Management History : Set
    soilN : SoilN
    soilC : SoilC
    moisture : Moisture
    hydrology : Hydrology
    temperature : Temperature
    precipitation : Precipitation
    habitat : Habitat
    biodiversity : Biodiversity
    disturbance : Disturbance
    management : Management
    history : History

open EcologicalLESState public

------------------------------------------------------------------------
-- Authority is an independent fibre, not another LES-predicted dependent
-- variable.  It meets technical/model fibres only at a decision interface.
------------------------------------------------------------------------

record AuthorityFibre : Set₁ where
  constructor authority-fibre
  field
    AffectedCountry CommunityAuthoritySource DecisionAuthority PermissionConsent
      ObligationCarrier Provenance TemporalValidity ScopeOfPermission : Set
    affectedCountry : AffectedCountry
    communityAuthoritySource : CommunityAuthoritySource
    decisionAuthority : DecisionAuthority
    permissionConsent : PermissionConsent
    obligationCarrier : ObligationCarrier
    provenance : Provenance
    temporalValidity : TemporalValidity
    scopeOfPermission : ScopeOfPermission
    authorityReference : String

open AuthorityFibre public

------------------------------------------------------------------------
-- Consumer-specific requirement vectors.
------------------------------------------------------------------------

data RequirementCoordinate : Set where
  sourceIdentity : RequirementCoordinate
  inputVersionIdentity : RequirementCoordinate
  modelEquationIdentity : RequirementCoordinate
  exactReplay : RequirementCoordinate
  biologicalAdequacy : RequirementCoordinate
  localSoilClimateAdequacy : RequirementCoordinate
  farmUnitEconomics : RequirementCoordinate
  uncertaintyAdequacy : RequirementCoordinate
  climateAccountingAdequacy : RequirementCoordinate
  ecologicalAdequacy : RequirementCoordinate
  hydrologyAdequacy : RequirementCoordinate
  distributionAdequacy : RequirementCoordinate
  authorityAdequacy : RequirementCoordinate


requiredFor : BNFConsumerQuestion → RequirementCoordinate → Bool
requiredFor replayNationalAvoidedUreaExpenditure sourceIdentity = true
requiredFor replayNationalAvoidedUreaExpenditure inputVersionIdentity = true
requiredFor replayNationalAvoidedUreaExpenditure modelEquationIdentity = true
requiredFor replayNationalAvoidedUreaExpenditure exactReplay = true
requiredFor replayNationalAvoidedUreaExpenditure _ = false

requiredFor estimateNationalAvoidedCO2e sourceIdentity = true
requiredFor estimateNationalAvoidedCO2e inputVersionIdentity = true
requiredFor estimateNationalAvoidedCO2e modelEquationIdentity = true
requiredFor estimateNationalAvoidedCO2e exactReplay = true
requiredFor estimateNationalAvoidedCO2e climateAccountingAdequacy = true
requiredFor estimateNationalAvoidedCO2e _ = false

requiredFor predictLocalSoybeanYield biologicalAdequacy = true
requiredFor predictLocalSoybeanYield localSoilClimateAdequacy = true
requiredFor predictLocalSoybeanYield uncertaintyAdequacy = true
requiredFor predictLocalSoybeanYield _ = false

requiredFor estimateFarmNetBenefit biologicalAdequacy = true
requiredFor estimateFarmNetBenefit localSoilClimateAdequacy = true
requiredFor estimateFarmNetBenefit farmUnitEconomics = true
requiredFor estimateFarmNetBenefit uncertaintyAdequacy = true
requiredFor estimateFarmNetBenefit _ = false

requiredFor predictEcologicalResponse biologicalAdequacy = true
requiredFor predictEcologicalResponse localSoilClimateAdequacy = true
requiredFor predictEcologicalResponse climateAccountingAdequacy = true
requiredFor predictEcologicalResponse ecologicalAdequacy = true
requiredFor predictEcologicalResponse hydrologyAdequacy = true
requiredFor predictEcologicalResponse uncertaintyAdequacy = true
requiredFor predictEcologicalResponse _ = false

requiredFor decideLandscapeIntervention biologicalAdequacy = true
requiredFor decideLandscapeIntervention localSoilClimateAdequacy = true
requiredFor decideLandscapeIntervention farmUnitEconomics = true
requiredFor decideLandscapeIntervention climateAccountingAdequacy = true
requiredFor decideLandscapeIntervention ecologicalAdequacy = true
requiredFor decideLandscapeIntervention hydrologyAdequacy = true
requiredFor decideLandscapeIntervention distributionAdequacy = true
requiredFor decideLandscapeIntervention uncertaintyAdequacy = true
requiredFor decideLandscapeIntervention _ = false

requiredFor decideCountryAffectingIntervention biologicalAdequacy = true
requiredFor decideCountryAffectingIntervention localSoilClimateAdequacy = true
requiredFor decideCountryAffectingIntervention farmUnitEconomics = true
requiredFor decideCountryAffectingIntervention climateAccountingAdequacy = true
requiredFor decideCountryAffectingIntervention ecologicalAdequacy = true
requiredFor decideCountryAffectingIntervention hydrologyAdequacy = true
requiredFor decideCountryAffectingIntervention distributionAdequacy = true
requiredFor decideCountryAffectingIntervention uncertaintyAdequacy = true
requiredFor decideCountryAffectingIntervention authorityAdequacy = true
requiredFor decideCountryAffectingIntervention _ = false

researchReplayDoesNotRequireAuthority :
  requiredFor replayNationalAvoidedUreaExpenditure authorityAdequacy ≡ false
researchReplayDoesNotRequireAuthority = refl

countryAffectingDecisionRequiresAuthority :
  requiredFor decideCountryAffectingIntervention authorityAdequacy ≡ true
countryAffectingDecisionRequiresAuthority = refl

farmQuestionRequiresUnitEconomics :
  requiredFor estimateFarmNetBenefit farmUnitEconomics ≡ true
farmQuestionRequiresUnitEconomics = refl

------------------------------------------------------------------------
-- BNF counterfactual contract shape.
------------------------------------------------------------------------

record BNFCounterfactualMeaning : Set₁ where
  constructor bnf-counterfactual-meaning
  field
    sameCropTarget : Set
    sameAreaTarget : Set
    sameYieldTargetOrExplicitYieldModel : Set
    effectiveBNFRemoved : Set
    mineralNSubstitutionRule : Set
    secondaryNRule : Set
    temporalAlignment : Set
    spatialAlignment : Set
    heldFixedJustification : Set
    meaningReference : String

open BNFCounterfactualMeaning public

counterfactualBoundary : Counterfactual.CounterfactualBoundary
counterfactualBoundary = Counterfactual.canonicalCounterfactualBoundary

------------------------------------------------------------------------
-- Qualified decision contract.  Requirements are independent receipts.
------------------------------------------------------------------------

record QualifiedIntervention (question : BNFConsumerQuestion) : Set₁ where
  constructor qualified-intervention
  field
    TechnicalAdequacy EmpiricalValidation EconomicAdequacy EcologicalAdequacy
      ClimateAccountingAdequacy AuthorityAdequacy : Set
    technicalAdequacy : TechnicalAdequacy
    empiricalValidation : EmpiricalValidation
    economicAdequacy : EconomicAdequacy
    ecologicalAdequacy : EcologicalAdequacy
    climateAccountingAdequacy : ClimateAccountingAdequacy
    authorityAdequacy : AuthorityAdequacy
    declaredQuestion : BNFConsumerQuestion
    questionMatches : declaredQuestion ≡ question

open QualifiedIntervention public

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data NationalEconomicReplayImpliesFarmRealisationPermission : Set where

data SameCO2eNumberImpliesSameClimateAccountingObjectPermission : Set where

data AvoidedCO2eImpliesEcologicalOutcomePermission : Set where

data EconomicAdequacyImpliesEcologicalAdequacyPermission : Set where

data EcologicalAdequacyImpliesCountryAuthorityAdequacyPermission : Set where

data ModelFibreImpliesAuthorityFibrePermission : Set where

data AuthorityFibreImpliesEmpiricalAccuracyPermission : Set where

nationalReplayDoesNotAutoPromoteToFarmRealisation :
  NationalEconomicReplayImpliesFarmRealisationPermission → ⊥
nationalReplayDoesNotAutoPromoteToFarmRealisation ()

sameCO2eNumberDoesNotIdentifyAccountingObject :
  SameCO2eNumberImpliesSameClimateAccountingObjectPermission → ⊥
sameCO2eNumberDoesNotIdentifyAccountingObject ()

avoidedCO2eDoesNotAutoPromoteToEcologicalOutcome :
  AvoidedCO2eImpliesEcologicalOutcomePermission → ⊥
avoidedCO2eDoesNotAutoPromoteToEcologicalOutcome ()

economicAdequacyDoesNotAutoPromoteToEcologicalAdequacy :
  EconomicAdequacyImpliesEcologicalAdequacyPermission → ⊥
economicAdequacyDoesNotAutoPromoteToEcologicalAdequacy ()

ecologicalAdequacyDoesNotAutoPromoteToCountryAuthority :
  EcologicalAdequacyImpliesCountryAuthorityAdequacyPermission → ⊥
ecologicalAdequacyDoesNotAutoPromoteToCountryAuthority ()

modelFibreDoesNotAutoPromoteToAuthorityFibre :
  ModelFibreImpliesAuthorityFibrePermission → ⊥
modelFibreDoesNotAutoPromoteToAuthorityFibre ()

authorityFibreDoesNotAutoPromoteToEmpiricalAccuracy :
  AuthorityFibreImpliesEmpiricalAccuracyPermission → ⊥
authorityFibreDoesNotAutoPromoteToEmpiricalAccuracy ()

------------------------------------------------------------------------
-- Reuse exact generic and domain boundaries.
------------------------------------------------------------------------

consumerIndexedBoundary : Fibre.ConsumerIndexedModelBoundary
consumerIndexedBoundary = Fibre.canonicalConsumerIndexedModelBoundary

modelAdequacyBoundary : Adequacy.ModelAdequacyBoundary
modelAdequacyBoundary = Adequacy.canonicalModelAdequacyBoundary

nationalSavingsStillDoesNotMeanTerminalFarmerBenefit =
  Econ.nationalAvoidedCostDoesNotAutoPromoteToTerminalFarmerBenefit

technicalBundleStillDoesNotCreateQualifiedUse =
  Cross.technicalBundleDoesNotAutoPromoteToQualifiedUse

indigenousOrderStillNotCreatedByExternalRecognition :
  TwoOrder.externalRecognitionCreatesOrder TwoOrder.indigenousOrderFibre ≡ false
indigenousOrderStillNotCreatedByExternalRecognition = refl

quoteStillDoesNotSupplyCalculationReplay =
  Attribution.speakerQuoteDoesNotSupplyCalculationReplay
