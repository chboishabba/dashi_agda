module DASHI.Wikimedia.IbrahimSnowballAIStateMilitaryChipClimateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Governance.PalantirPlatformCapabilityEvidenceExact as Palantir
import DASHI.Economics.ChinaUSAITrainingServingComputeSeparation2026Exact as ChinaUS
import DASHI.Economics.TSMCHBMManufacturingDemandPolicy2026Exact as TSMC
import DASHI.Planning.DataCentreUrbanResourceConflictExact as DataCentre
import DASHI.Biology.DeepTimeCarbonBiosphereFossilFuelBidiExact as Fossil

------------------------------------------------------------------------
-- IBRAHIM/SNOWBALL CROSS-DOMAIN WALK:
-- AI LABS / STATE-MILITARY POWER / PLATFORM PARTNERS / CHIP SUPPLY / CLIMATE
--
-- Public-source observations inspected 2026-09-10 are intentionally role-bound.
-- Verified examples include:
--   * Anthropic 2025 DoD prototype agreement (ceiling USD 200m);
--   * Anthropic statements that Claude was integrated with Palantir workflows
--     on classified networks for US defense/intelligence use;
--   * Anthropic's 2026 dispute with the Pentagon over mass domestic
--     surveillance and fully autonomous weapons safeguards;
--   * OpenAI's 2025 DoD prototype and 2026 classified/GenAI.mil deployments;
--   * Reuters 2026 reporting that DeepSeek is developing an inference chip and
--     has increasingly used Huawei hardware under Nvidia export restrictions;
--   * separate reporting that Huawei is central to China's domestic advanced
--     chip/equipment ecosystem.
--
-- These facts do NOT imply moral equivalence, operational use in a particular
-- strike, a specific Palantir deployment's subject-level data, or that Huawei
-- is the foundry/manufacturer for DeepSeek's chip.
------------------------------------------------------------------------

data PublicFactRole : Set where
  companyOfficialStatement
  governmentContractRecord
  judicialRuling
  reputableNewsReport
  wikidataIdentityOnly : PublicFactRole

record PublicFact : Set where
  constructor public-fact
  field
    subject : String
    proposition : String
    sourceReference : String
    role : PublicFactRole
    observationDate : String
    excludedInference : String
open PublicFact public

anthropicDoDFact : PublicFact
anthropicDoDFact = public-fact
  "Anthropic"
  "Anthropic announced a two-year US Department of Defense prototype agreement with a USD 200 million ceiling in July 2025."
  "Anthropic, Anthropic and the Department of Defense to advance responsible AI in defense operations, 2025-07-14"
  companyOfficialStatement
  "2026-09-10"
  "Contract existence does not establish every downstream operational use, weapon involvement, legality, or moral conclusion."

anthropicPalantirFact : PublicFact
anthropicPalantirFact = public-fact
  "Anthropic / Palantir"
  "Anthropic states that Claude has been integrated into Palantir mission workflows on classified networks for US defense and intelligence organisations."
  "Anthropic DoD announcement 2025-07-14; Anthropic/Palantir/AWS partnership announcement 2024-11"
  companyOfficialStatement
  "2026-09-10"
  "Partnership and classified-network availability do not identify subject-level data, a particular operational decision, or abuse."

anthropicGuardrailDisputeFact : PublicFact
anthropicGuardrailDisputeFact = public-fact
  "Anthropic / US Department of Defense"
  "Anthropic publicly stated in February 2026 that it objected to mass domestic surveillance and fully autonomous weapons uses; the Pentagon later designated Anthropic a supply-chain risk, and a federal judge blocked the blacklisting in August 2026."
  "Anthropic statements 2026-02-26/27; Reuters report on US district court ruling 2026-08-28"
  judicialRuling
  "2026-09-10"
  "A policy dispute and court ruling do not imply that all military AI use is unlawful, nor that Anthropic rejects military assistance generally."

openAIDefenseFact : PublicFact
openAIDefenseFact = public-fact
  "OpenAI"
  "OpenAI announced a USD 200 million-ceiling DoD pilot in 2025 and expanded US national-security deployments in 2026, including GenAI.mil and a classified Pentagon agreement with stated guardrails."
  "OpenAI for Government 2025-06-16; Bringing ChatGPT to GenAI.mil 2026-02-09; Our agreement with the Department of War 2026-02-28"
  companyOfficialStatement
  "2026-09-10"
  "Similar customer category does not imply identical safeguards, operational uses, contracts, politics, or outcomes across AI labs."

deepSeekChipFact : PublicFact
deepSeekChipFact = public-fact
  "DeepSeek"
  "Reuters reported in July 2026 that DeepSeek is developing an inference chip and has increasingly leaned on Huawei hardware under US restrictions on advanced Nvidia chips."
  "Reuters, China's DeepSeek developing its own AI chip, 2026-07-07"
  reputableNewsReport
  "2026-09-10"
  "Chip design effort and Huawei hardware use do not establish Huawei as foundry or manufacturer of DeepSeek's chip."

huaweiDomesticChipFact : PublicFact
huaweiDomesticChipFact = public-fact
  "Huawei / China semiconductor ecosystem"
  "Recent reporting places Huawei at the centre of China's effort to reduce reliance on foreign semiconductor technology, including support for domestic advanced chipmaking equipment and AI accelerators."
  "Financial Times / Reuters reporting inspected 2026-09-10"
  reputableNewsReport
  "2026-09-10"
  "Ecosystem centrality does not identify every chip designer, foundry, lithography supplier, or manufacturing relationship with Huawei."

anthropicPowerFact : PublicFact
anthropicPowerFact = public-fact
  "Anthropic"
  "Anthropic stated in February 2026 that frontier-model training will require gigawatt-scale power and committed to cover certain consumer electricity-price increases attributable to its data centres."
  "Anthropic, Covering electricity price increases from our data centers, 2026-02-11"
  companyOfficialStatement
  "2026-09-10"
  "Electricity demand does not by itself establish a fossil-fuel generation share, exact emissions quantity, or local climate harm."

------------------------------------------------------------------------
-- External identities: requested/retained when safely resolvable.
------------------------------------------------------------------------

anthropicQid : Identity.ExternalIdentityDemand
anthropicQid = Identity.mkOptionalIdentityDemand
  "AI state-power snowball" "company identity" "Anthropic"
  Identity.wikidataQid
  (Identity.verified "Q116758847" "Wikidata identity checked 2026-09-10")

palantirQid : Identity.ExternalIdentityDemand
palantirQid = Identity.mkOptionalIdentityDemand
  "AI state-power snowball" "company identity" "Palantir Technologies"
  Identity.wikidataQid
  (Identity.verified "Q2047336" "Wikidata identity checked 2026-09-10")

openAIQid : Identity.ExternalIdentityDemand
openAIQid = Identity.mkOptionalIdentityDemand
  "AI state-power snowball" "organisation identity" "OpenAI"
  Identity.wikidataQid
  (Identity.verified "Q21708200" "Wikidata research-organisation identity checked 2026-09-10; current corporate subsidiaries remain distinct")

deepSeekQid : Identity.ExternalIdentityDemand
deepSeekQid = Identity.mkOptionalIdentityDemand
  "AI state-power snowball" "company identity" "DeepSeek"
  Identity.wikidataQid
  (Identity.verified "Q131577453" "Wikidata identity checked 2026-09-10")

huaweiQid : Identity.ExternalIdentityDemand
huaweiQid = Identity.mkOptionalIdentityDemand
  "AI state-power snowball" "company identity" "Huawei"
  Identity.wikidataQid
  (Identity.verified "Q160120" "Wikidata identity checked 2026-09-10")

tsmcQid : Identity.ExternalIdentityDemand
tsmcQid = Identity.mkOptionalIdentityDemand
  "AI state-power snowball" "foundry identity" "TSMC"
  Identity.wikidataQid
  (Identity.verified "Q713418" "Wikidata identity checked 2026-09-10")

nvidiaQid : Identity.ExternalIdentityDemand
nvidiaQid = Identity.mkOptionalIdentityDemand
  "AI state-power snowball" "accelerator supplier identity" "Nvidia"
  Identity.wikidataQid
  (Identity.verified "Q182477" "Wikidata identity checked 2026-09-10")

------------------------------------------------------------------------
-- Snowball witness 1: same military-AI supplier surface cannot recover safety
-- / usage-policy stance or the legal status of a government dispute.
------------------------------------------------------------------------

data MilitaryAISupplierCase : Set where
  supplierWithAutonomousWeaponGuardrail : MilitaryAISupplierCase
  supplierWithDifferentContractGuardrails : MilitaryAISupplierCase

data MilitarySupplierSurface : Set where
  frontierLabServingUSDefense : MilitarySupplierSurface

data GuardrailReading : Set where
  explicitMassSurveillanceAndFullAutonomyExceptions : GuardrailReading
  otherContractualSafetyArchitecture : GuardrailReading

militarySurface : MilitaryAISupplierCase → MilitarySupplierSurface
militarySurface _ = frontierLabServingUSDefense

guardrailReading : MilitaryAISupplierCase → GuardrailReading
guardrailReading supplierWithAutonomousWeaponGuardrail =
  explicitMassSurveillanceAndFullAutonomyExceptions
guardrailReading supplierWithDifferentContractGuardrails =
  otherContractualSafetyArchitecture

militarySurfaceGuardrailDefect :
  INF.NonFactorabilityWitness militarySurface guardrailReading
militarySurfaceGuardrailDefect = INF.nonFactorabilityWitness
  supplierWithAutonomousWeaponGuardrail
  supplierWithDifferentContractGuardrails
  refl
  (λ ())

militarySupplierCannotFactorGuardrailPolicy :
  INF.FactorsThrough militarySurface guardrailReading → ⊥
militarySupplierCannotFactorGuardrailPolicy =
  INF.witnessRulesOutEveryFlatFactorisation militarySurfaceGuardrailDefect

------------------------------------------------------------------------
-- Snowball witness 2: chip ecosystem adjacency cannot recover producer role.
------------------------------------------------------------------------

data ChipEcosystemCase : Set where
  designUsesExternalAccelerator : ChipEcosystemCase
  designHasUnresolvedFoundry : ChipEcosystemCase

data ChipAdjacencySurface : Set where
  chinaAIChipIndependenceSurface : ChipAdjacencySurface

data ChipProducerRole : Set where
  acceleratorSupplierRole : ChipProducerRole
  foundryUnresolvedRole : ChipProducerRole

chipAdjacency : ChipEcosystemCase → ChipAdjacencySurface
chipAdjacency _ = chinaAIChipIndependenceSurface

chipProducer : ChipEcosystemCase → ChipProducerRole
chipProducer designUsesExternalAccelerator = acceleratorSupplierRole
chipProducer designHasUnresolvedFoundry = foundryUnresolvedRole

chipAdjacencyProducerDefect :
  INF.NonFactorabilityWitness chipAdjacency chipProducer
chipAdjacencyProducerDefect = INF.nonFactorabilityWitness
  designUsesExternalAccelerator designHasUnresolvedFoundry refl (λ ())

chipAdjacencyCannotFactorProducerRole :
  INF.FactorsThrough chipAdjacency chipProducer → ⊥
chipAdjacencyCannotFactorProducerRole =
  INF.witnessRulesOutEveryFlatFactorisation chipAdjacencyProducerDefect

------------------------------------------------------------------------
-- Snowball witness 3: compute/data-centre capacity does not determine climate
-- or fossil-fuel pathway.  Grid mix, temporal matching, local resource use and
-- upstream manufacturing remain consumer-indexed residuals.
------------------------------------------------------------------------

data ComputeCapacityCase : Set where
  sameComputeLowerCarbonGrid : ComputeCapacityCase
  sameComputeHigherFossilGrid : ComputeCapacityCase

data ComputeSurface : Set where
  sameFrontierComputeCapacity : ComputeSurface

data ClimateEnergyReading : Set where
  lowerCarbonElectricityPath : ClimateEnergyReading
  higherFossilElectricityPath : ClimateEnergyReading

computeSurface : ComputeCapacityCase → ComputeSurface
computeSurface _ = sameFrontierComputeCapacity

climateEnergyReading : ComputeCapacityCase → ClimateEnergyReading
climateEnergyReading sameComputeLowerCarbonGrid = lowerCarbonElectricityPath
climateEnergyReading sameComputeHigherFossilGrid = higherFossilElectricityPath

computeClimateDefect : INF.NonFactorabilityWitness computeSurface climateEnergyReading
computeClimateDefect = INF.nonFactorabilityWitness
  sameComputeLowerCarbonGrid sameComputeHigherFossilGrid refl (λ ())

computeCapacityCannotFactorClimatePath :
  INF.FactorsThrough computeSurface climateEnergyReading → ⊥
computeCapacityCannotFactorClimatePath =
  INF.witnessRulesOutEveryFlatFactorisation computeClimateDefect

------------------------------------------------------------------------
-- Cross-domain boundary: current names are exemplars; the invariant remains
-- consumer/query-relative and may snowball additional axes.
------------------------------------------------------------------------

record AIStateMilitaryChipClimateBoundary : Set where
  constructor ai-state-military-chip-climate-boundary
  field
    verifiedPartnershipSeparatedFromControversy : Bool
    companyStatementSeparatedFromCourtAndNews : Bool
    militaryCustomerCategoryDoesNotCreateMoralEquivalence : Bool
    palantirCapabilityDoesNotCreateDeploymentAbuse : Bool
    chipDesignerSupplierFoundryRolesSeparated : Bool
    deepSeekHuaweiFoundryRelationClaimed : Bool
    chipInventoryDoesNotDetermineCapability : Bool
    computeCapacityDoesNotDetermineClimatePath : Bool
    fossilFuelHistoryAndGridUseRemainDistinct : Bool
    attributionAndExternalIdentitySnowball : Bool
    currentAxisVocabularyClaimedComplete : Bool
open AIStateMilitaryChipClimateBoundary public

canonicalAIStateMilitaryChipClimateBoundary : AIStateMilitaryChipClimateBoundary
canonicalAIStateMilitaryChipClimateBoundary =
  ai-state-military-chip-climate-boundary
    true true true false true false true true true true false

------------------------------------------------------------------------
-- Existing substrate retained rather than duplicated.
------------------------------------------------------------------------

palantirBoundary : Palantir.PalantirCapabilityBoundary
palantirBoundary = Palantir.canonicalPalantirCapabilityBoundary

chinaComputeBoundary : ChinaUS.SourceBackedTrainingServingCalibration
chinaComputeBoundary = ChinaUS.canonicalSourceBackedTrainingServingCalibration

dataCentreCompetitionWitness :
  (DataCentre.SpatiallyOverlaps DataCentre.housingProject DataCentre.aiDataCentre → ⊥) ×
  DataCentre.CompetesFor DataCentre.housingProject DataCentre.aiDataCentre DataCentre.electricity
dataCentreCompetitionWitness = DataCentre.projectsNeedNotOverlapToCompeteForElectricity

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data AnthropicPalantirPartnershipMeansEveryPalantirUsePermission : Set where
data MilitaryAIProviderMeansAutonomousWeaponUsePermission : Set where
data DeepSeekUsesHuaweiMeansHuaweiFabricatesDeepSeekChipPermission : Set where
data DataCentreDemandMeansFossilFuelGenerationPermission : Set where
data ClimateCostMeansMilitaryUseConclusionPermission : Set where

anthropicPalantirDoesNotGeneraliseToEveryDeployment :
  AnthropicPalantirPartnershipMeansEveryPalantirUsePermission → ⊥
anthropicPalantirDoesNotGeneraliseToEveryDeployment ()

militaryProviderDoesNotProveAutonomousWeaponUse :
  MilitaryAIProviderMeansAutonomousWeaponUsePermission → ⊥
militaryProviderDoesNotProveAutonomousWeaponUse ()

deepSeekHuaweiDoesNotResolveFoundry :
  DeepSeekUsesHuaweiMeansHuaweiFabricatesDeepSeekChipPermission → ⊥
deepSeekHuaweiDoesNotResolveFoundry ()

dataCentreDemandDoesNotIdentifyGenerationMix :
  DataCentreDemandMeansFossilFuelGenerationPermission → ⊥
dataCentreDemandDoesNotIdentifyGenerationMix ()

climateCostDoesNotDetermineMilitaryEthics :
  ClimateCostMeansMilitaryUseConclusionPermission → ⊥
climateCostDoesNotDetermineMilitaryEthics ()
