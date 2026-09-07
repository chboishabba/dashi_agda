module DASHI.Economics.ClimateAIInfrastructureTransitionRiskCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.ClimateRateRecoveryIrreversibilityBidiExact as Climate
import DASHI.Governance.FeministClimateJusticeResidualBundleExact as Justice
import DASHI.Governance.TrumpEnergyCrackSpreadCrossPollinationExact as Energy
import DASHI.Economics.ManufacturingScarcityTimescaleExact as Manufacturing
import DASHI.Economics.PolicyBackstopCommercialDisciplineExact as Policy

------------------------------------------------------------------------
-- CLIMATE x AI INFRASTRUCTURE TRANSITION RISK
--
-- Structural reuse only.  The climate owners contribute path dependence,
-- endpoint-vs-history separation, independent recovery witnesses and residual
-- incidence axes.  They do not establish any empirical AI project outcome.
------------------------------------------------------------------------

data InfrastructureTransitionState : Set where
  preBuild
  capacityBuiltEconomicsIntact
  capacityBuiltEconomicsImpaired
  capacityRetrofittedButLegacyLossRetained
  : InfrastructureTransitionState

data CoarseCapacityShadow : Set where
  sameInstalledCapacity : CoarseCapacityShadow

capacityShadow : InfrastructureTransitionState → CoarseCapacityShadow
capacityShadow _ = sameInstalledCapacity

data CapitalHistoryResidue : Set where
  noCapitalResidue
  financingCommitmentRetained
  obsolescenceLossRetained
  policyLiabilityRetained
  : CapitalHistoryResidue

capitalResidue : InfrastructureTransitionState → CapitalHistoryResidue
capitalResidue preBuild = noCapitalResidue
capitalResidue capacityBuiltEconomicsIntact = financingCommitmentRetained
capitalResidue capacityBuiltEconomicsImpaired = obsolescenceLossRetained
capitalResidue capacityRetrofittedButLegacyLossRetained = policyLiabilityRetained

sameCapacityCanRetainDifferentCapitalHistory :
  capitalResidue preBuild ≡ capitalResidue capacityBuiltEconomicsImpaired → ⊥
sameCapacityCanRetainDifferentCapitalHistory ()

------------------------------------------------------------------------
-- Stranded-capital / transition-risk coordinates.
------------------------------------------------------------------------

data TransitionRiskCoordinate : Set where
  hardwareObsolescence
  softwareEfficiencyDeflation
  powerPriceExposure
  gridConnectionDelay
  waterConstraint
  refinancingConstraint
  demandRepricing
  policyChange
  exportControlChange
  geographicConcentration
  : TransitionRiskCoordinate

data IncidenceCoordinate : Set where
  equityHolderLoss
  creditorLoss
  publicSubsidyLoss
  utilityRatepayerBurden
  workerCommunityBurden
  customerPriceBurden
  foreignDependencyBurden
  : IncidenceCoordinate

record InfrastructureTransitionRiskReceipt : Set₁ where
  constructor infrastructureTransitionRiskReceipt
  field
    Asset : Set
    asset : Asset
    transitionCoordinate : TransitionRiskCoordinate
    Incidence : Set
    incidence : Incidence
    preTransitionValueReference : String
    postTransitionValueReference : String
    financingHistoryReference : String
    deploymentHistoryReference : String
    recoveryOrRepurposingReference : String
    validationReference : String

open InfrastructureTransitionRiskReceipt public

record TransitionIncidenceVector : Set₁ where
  constructor transitionIncidenceVector
  field
    PhenomenonResidual : Set
    EpistemicResidual : Set
    PoliticalResidual : Set
    ResponsibilityResidual : Set
    CategoryResidual : Set
    phenomenonResidual : PhenomenonResidual
    epistemicResidual : EpistemicResidual
    politicalResidual : PoliticalResidual
    responsibilityResidual : ResponsibilityResidual
    categoryResidual : CategoryResidual

open TransitionIncidenceVector public

------------------------------------------------------------------------
-- Existing climate / energy donors retained.
------------------------------------------------------------------------

climateRecoveryBoundary : Climate.ClimateRateRecoveryIrreversibilityBoundary
climateRecoveryBoundary = Climate.canonicalClimateRateRecoveryIrreversibilityBoundary

climateJusticeBoundary : Justice.FeministClimateResidualBoundary
climateJusticeBoundary = Justice.canonicalFeministClimateResidualBoundary

energyMarketBoundary : Energy.TrumpEnergyCrackSpreadBoundary
energyMarketBoundary = Energy.canonicalTrumpEnergyCrackSpreadBoundary

------------------------------------------------------------------------
-- Rate and trajectory can matter even if coarse endpoints later coincide.
------------------------------------------------------------------------

record BuildoutRatePath : Set₁ where
  constructor buildoutRatePath
  field
    CapacityEndpoint : Set
    capacityEndpoint : CapacityEndpoint
    BuildoutRate : Set
    buildoutRate : BuildoutRate
    FinancingPath : Set
    financingPath : FinancingPath
    TechnologyPath : Set
    technologyPath : TechnologyPath

open BuildoutRatePath public

data SameCapacityEndpointImpliesSameCapitalStatePermission : Set where

data RestoredUtilisationImpliesRestoredAssetValuePermission : Set where

data RefinanceSuccessImpliesHistoricalLossErasedPermission : Set where

data TechnicalRecoveryClosesResponsibilityResidualPermission : Set where

data PolicySupportTransfersNoPublicRiskPermission : Set where

data EnergyPriceAloneDeterminesAIInfrastructureViabilityPermission : Set where

data ClimateDomainEqualsAIInfrastructureDomainPermission : Set where

sameCapacityEndpointDoesNotAutoPromoteToSameCapitalState :
  SameCapacityEndpointImpliesSameCapitalStatePermission → ⊥
sameCapacityEndpointDoesNotAutoPromoteToSameCapitalState ()

restoredUtilisationDoesNotAutoPromoteToRestoredAssetValue :
  RestoredUtilisationImpliesRestoredAssetValuePermission → ⊥
restoredUtilisationDoesNotAutoPromoteToRestoredAssetValue ()

refinanceSuccessDoesNotEraseHistoricalLoss :
  RefinanceSuccessImpliesHistoricalLossErasedPermission → ⊥
refinanceSuccessDoesNotEraseHistoricalLoss ()

technicalRecoveryDoesNotCloseResponsibilityResidual :
  TechnicalRecoveryClosesResponsibilityResidualPermission → ⊥
technicalRecoveryDoesNotCloseResponsibilityResidual ()

policySupportDoesNotTransferNoPublicRisk :
  PolicySupportTransfersNoPublicRiskPermission → ⊥
policySupportDoesNotTransferNoPublicRisk ()

energyPriceAloneDoesNotDetermineAIInfrastructureViability :
  EnergyPriceAloneDeterminesAIInfrastructureViabilityPermission → ⊥
energyPriceAloneDoesNotDetermineAIInfrastructureViability ()

climateDomainDoesNotBecomeAIInfrastructureDomain :
  ClimateDomainEqualsAIInfrastructureDomainPermission → ⊥
climateDomainDoesNotBecomeAIInfrastructureDomain ()

------------------------------------------------------------------------
-- Positive reopening / recovery discipline.
------------------------------------------------------------------------

data TransitionRecoveryClaim : Set where
  strandedAssetRecovered
  publicSupportNetBeneficial
  dependencyReduced
  communityBurdenResolved
  : TransitionRecoveryClaim

data TransitionRecoveryProducer : Set where
  independentAssetRecoveryProducer
  fullPublicIncidenceProducer
  supplyChainDependencyProducer
  distributionalOutcomeProducer
  : TransitionRecoveryProducer

requiredTransitionProducer : TransitionRecoveryClaim → TransitionRecoveryProducer
requiredTransitionProducer strandedAssetRecovered = independentAssetRecoveryProducer
requiredTransitionProducer publicSupportNetBeneficial = fullPublicIncidenceProducer
requiredTransitionProducer dependencyReduced = supplyChainDependencyProducer
requiredTransitionProducer communityBurdenResolved = distributionalOutcomeProducer

scarcityStillDoesNotCloseDownstreamViability :
  Manufacturing.ScarcityRentImpliesDownstreamViabilityPermission → ⊥
scarcityStillDoesNotCloseDownstreamViability =
  Manufacturing.scarcityRentDoesNotAutoPromoteToDownstreamViability

policyStillDoesNotCloseCommercialViability :
  Policy.PolicySupportImpliesCommercialViabilityPermission → ⊥
policyStillDoesNotCloseCommercialViability =
  Policy.policySupportDoesNotAutoPromoteToCommercialViability
