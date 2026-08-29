module DASHI.Environment.SoilBiogeochemistryProcessNetworkExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Environment.QuantitiesConservation as Conservation
import DASHI.Environment.RootSoilFungalIonWaterPhysiologyExact as RootSoilFungal
import DASHI.Environment.LESDomainBasisBidiFrontierExact as Basis

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Stefano Manzoni and Amilcare Porporato,
-- "Soil carbon and nitrogen mineralization: Theory and models across scales",
-- Soil Biology and Biochemistry 41(7) (2009), 1355--1379.
-- DOI: 10.1016/j.soilbio.2009.02.031.
--
-- SOURCE BOUNDARY
-- The review establishes the broad modelling architecture of soil C/N
-- biogeochemistry in terms of decomposition, microbial biomass,
-- mineralisation/immobilisation, heterotrophic respiration, kinetic and
-- stoichiometric constraints, with explicit attention to scale dependence.
--
-- The exact Agda pool/process types and cross-welds below are DASHI formal
-- reconstruction. No particular rate law, pool count, parameter value or
-- universal scale transfer is attributed to the source.
------------------------------------------------------------------------

data SoilCNPoolKind : Set where
  soilOrganicCarbon
  microbialBiomassCarbon
  soilOrganicNitrogen
  mineralNitrogen
  microbialBiomassNitrogen
  : SoilCNPoolKind

data SoilCNProcessKind : Set where
  decomposition
  microbialAssimilation
  mineralisation
  immobilisation
  heterotrophicRespiration
  : SoilCNProcessKind

record SoilCNPool : Set where
  constructor soilCNPool
  field
    poolId : String
    kind : SoilCNPoolKind
    chemistryCompartmentReference : String
    stateCarrierReference : String
    evidenceReference : String

open SoilCNPool public

record SoilCNProcess : Set where
  constructor soilCNProcess
  field
    processId : String
    kind : SoilCNProcessKind
    chemistryTransition : Chemistry.Transition
    sourcePools : List SoilCNPool
    targetPools : List SoilCNPool
    kineticLawReference : String
    stoichiometricConstraintReference : String
    moistureDependenceReference : String
    temperatureDependenceReference : String
    spatialScaleReference : String
    temporalScaleReference : String
    parameterAuthorityReference : String

open SoilCNProcess public

------------------------------------------------------------------------
-- Model-relative C/N process network.
------------------------------------------------------------------------

record SoilCNProcessNetwork : Set where
  constructor soilCNProcessNetwork
  field
    chemistryNetwork : Chemistry.ReactionNetwork
    pools : List SoilCNPool
    processes : List SoilCNProcess
    carbonBalance : Conservation.CarbonBalance
    nitrogenBalance : Conservation.NitrogenBalance

    microbialStateReference : String
    soilMoistureStateReference : String
    soilTemperatureStateReference : String
    gasExchangeOrRespirationReference : String
    scaleConsistencyReference : String
    residualInterpretationReference : String

open SoilCNProcessNetwork public

------------------------------------------------------------------------
-- Root/fungal coupling.
--
-- The soil process model does not infer plant/fungal exchange merely because
-- the same elements appear in both domains. A real realization supplies
-- explicit root-soil mechanisms and optional mycorrhizal extensions.
------------------------------------------------------------------------

record SoilPlantFungalBiogeochemistryWeld
    (soil : SoilCNProcessNetwork) : Set₁ where
  constructor soilPlantFungalBiogeochemistryWeld
  field
    rootSoilMechanism : RootSoilFungal.RootSoilIonWaterMechanism
    mycorrhizalExtensions :
      List (RootSoilFungal.MycorrhizalIonWaterExtension rootSoilMechanism)

    mineralNitrogenToRootSpeciesReference : String
    organicCarbonToPlantFungalCostReference : String
    rhizosphereChemistryReference : String
    waterProcessCommonStateReference : String
    uptakeAndMineralisationTimeScaleReference : String
    crossDomainConservationReference : String
    validationReference : String

open SoilPlantFungalBiogeochemistryWeld public

record SoilBiogeochemistryDomainRealization : Set₁ where
  constructor soilBiogeochemistryDomainRealization
  field
    domainMechanism : Basis.DomainMechanismSocket
    soilCN : SoilCNProcessNetwork
    plantFungalWelds : List (SoilPlantFungalBiogeochemistryWeld soilCN)

    stateIdentificationReference : String
    controlIdentificationReference : String
    observationIdentificationReference : String
    discrepancyModelReference : String
    experimentDesignReference : String
    identifiabilityReference : String
    heldOutValidationReference : String

open SoilBiogeochemistryDomainRealization public

sourceDOI : String
sourceDOI = "10.1016/j.soilbio.2009.02.031"

record SoilBiogeochemistryBoundary : Set where
  constructor soilBiogeochemistryBoundary
  field
    processKindChoosesUniversalRateLaw : Bool
    processKindChoosesUniversalRateLawIsFalse :
      processKindChoosesUniversalRateLaw ≡ false

    carbonNitrogenAccountingProvesMechanism : Bool
    carbonNitrogenAccountingProvesMechanismIsFalse :
      carbonNitrogenAccountingProvesMechanism ≡ false

    modelAtOneScaleAutomaticallyTransfersToAnother : Bool
    modelAtOneScaleAutomaticallyTransfersToAnotherIsFalse :
      modelAtOneScaleAutomaticallyTransfersToAnother ≡ false

    sharedElementNameProvesRootSoilFluxIdentity : Bool
    sharedElementNameProvesRootSoilFluxIdentityIsFalse :
      sharedElementNameProvesRootSoilFluxIdentity ≡ false

    explicitCrossDomainWeldRequired : Bool
    explicitCrossDomainWeldRequiredIsTrue :
      explicitCrossDomainWeldRequired ≡ true

    stage7ValidationStillRequired : Bool
    stage7ValidationStillRequiredIsTrue :
      stage7ValidationStillRequired ≡ true

canonicalSoilBiogeochemistryBoundary : SoilBiogeochemistryBoundary
canonicalSoilBiogeochemistryBoundary =
  soilBiogeochemistryBoundary
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
