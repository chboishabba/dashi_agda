module DASHI.Environment.SoilCarbonForestryManagementCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Environment.PluralSustainableLandManagementTraditionsExact as Plural
import DASHI.Environment.SustainableAgricultureManagementExact as Base
import DASHI.Environment.SoilBiogeochemistryProcessNetworkExact as Soil

------------------------------------------------------------------------
-- SOIL-CARBON / FORESTRY / CONSERVATION CROSS-POLLINATION
--
-- Carbon-oriented management, conservation agriculture, silviculture and
-- syntropic farming overlap in some mechanisms but are not synonyms.
------------------------------------------------------------------------

data SoilCarbonManagementLever : Set where
  retainLivingRoots
  retainSurfaceResidue
  returnWoodyBiomass
  addStableCarbonMaterial
  reduceMechanicalDisturbance
  diversifyPlantCommunity
  integrateWoodyPerennials
  manageGrazingReturn
  increaseOrganicAmendment
  manageForestRegeneration : SoilCarbonManagementLever

data CarbonMeasurementCoordinate : Set where
  soilOrganicCarbonStock
  soilOrganicMatterProxy
  abovegroundBiomassCarbon
  belowgroundBiomassCarbon
  deadwoodCarbon
  litterCarbon
  greenhouseGasFlux
  wholeSystemCarbonBalance : CarbonMeasurementCoordinate

record CarbonManagementCandidate : Set where
  constructor carbon-management-candidate
  field
    practice : Plural.ExtendedManagementPractice
    lever : SoilCarbonManagementLever
    coordinate : CarbonMeasurementCoordinate
    baselineReference : String
    samplingDepthReference : String
    timeHorizonReference : String
    measurementReference : String
    attributionReference : String

open CarbonManagementCandidate public

------------------------------------------------------------------------
-- Conservation agriculture is a three-principle system, not just no-till.
------------------------------------------------------------------------

record ConservationAgricultureRealisation : Set where
  constructor conservation-agriculture-realisation
  field
    minimumMechanicalDisturbance : Bool
    permanentOrganicSoilCover : Bool
    cropSpeciesDiversification : Bool
    localAdaptationReference : String
    soilCarbonOutcomeReference : String

open ConservationAgricultureRealisation public

canonicalConservationAgricultureShape : ConservationAgricultureRealisation
canonicalConservationAgricultureShape =
  conservation-agriculture-realisation
    true true true
    "FAO Conservation Agriculture: principles adapted to local conditions and needs"
    "Carbon outcome remains measured rather than definitionally positive"

------------------------------------------------------------------------
-- Regenerative agriculture remains an umbrella with contested definitions.
------------------------------------------------------------------------

record RegenerativeAgricultureClaim : Set where
  constructor regenerative-agriculture-claim
  field
    processDefinitionReference : String
    outcomeDefinitionReference : String
    certificationOrLegalDefinitionReference : String
    particularPracticesReference : String
    measuredOutcomesReference : String

open RegenerativeAgricultureClaim public

regenerativeDefinitionBoundary : RegenerativeAgricultureClaim
regenerativeDefinitionBoundary = regenerative-agriculture-claim
  "Some definitions are process-based: cover crops, livestock integration, reduced tillage, etc."
  "Some definitions are outcome-based: soil health, biodiversity, carbon or social outcomes."
  "No single widely accepted legal/regulatory definition is assumed."
  "Every concrete implementation must enumerate actual management practices."
  "Outcome claims require measurement and causal identification separately."

------------------------------------------------------------------------
-- Silviculture and syntropic farming overlap in woody vegetation management,
-- but one is general forest tending while the other is an agricultural system.
------------------------------------------------------------------------

record SilviculturalManagementReceipt : Set where
  constructor silvicultural-management-receipt
  field
    establishmentControlReference : String
    growthControlReference : String
    compositionControlReference : String
    healthQualityReference : String
    managementObjectiveReference : String
    carbonObjectiveIfAny : String

open SilviculturalManagementReceipt public

record SyntropicSilvicultureComparison : Set where
  constructor syntropic-silviculture-comparison
  field
    syntropicUsesWoodyStrata : Bool
    syntropicUsesSuccession : Bool
    silvicultureManagesWoodyEstablishmentAndGrowth : Bool
    sameTechnique : Bool
    sharedMechanismDoesNotErasePurposeDifference : Bool

open SyntropicSilvicultureComparison public

canonicalSyntropicSilvicultureComparison : SyntropicSilvicultureComparison
canonicalSyntropicSilvicultureComparison =
  syntropic-silviculture-comparison true true true false true

------------------------------------------------------------------------
-- Same-object weld back to the existing soil C/N process network.
------------------------------------------------------------------------

record SoilCarbonProcessWeld
    (soil : Soil.SoilCNProcessNetwork)
    (candidate : CarbonManagementCandidate) : Set₁ where
  constructor soil-carbon-process-weld
  field
    sameSoilNetwork : Soil.SoilCNProcessNetwork
    sameSoil : sameSoilNetwork ≡ soil
    affectedPoolOrProcessReference : String
    carbonBalanceReference : String
    nitrogenInteractionReference : String
    decompositionOrRespirationReference : String
    measuredCarbonReceipt : String

open SoilCarbonProcessWeld public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SilvicultureMeansCarbonSequestrationPermission : Set where

data ConservationAgricultureMeansNoTillOnlyPermission : Set where

data RegenerativeLabelMeansDefinedProtocolPermission : Set where

data CarbonPracticeMeansPermanentStoragePermission : Set where

data MoreBiomassMeansMoreSoilCarbonPermission : Set where

data SyntropicMeansSilviculturePermission : Set where

data SoilCarbonMeansWholeFarmClimateBenefitPermission : Set where

silvicultureDoesNotDefinitionallySequesterCarbon : SilvicultureMeansCarbonSequestrationPermission → ⊥
silvicultureDoesNotDefinitionallySequesterCarbon ()

conservationAgricultureIsNotNoTillAlone : ConservationAgricultureMeansNoTillOnlyPermission → ⊥
conservationAgricultureIsNotNoTillAlone ()

regenerativeLabelDoesNotDetermineProtocol : RegenerativeLabelMeansDefinedProtocolPermission → ⊥
regenerativeLabelDoesNotDetermineProtocol ()

carbonPracticeDoesNotGuaranteePermanentStorage : CarbonPracticeMeansPermanentStoragePermission → ⊥
carbonPracticeDoesNotGuaranteePermanentStorage ()

biomassIncreaseDoesNotByItselfProveSoilCarbonIncrease : MoreBiomassMeansMoreSoilCarbonPermission → ⊥
biomassIncreaseDoesNotByItselfProveSoilCarbonIncrease ()

syntropicAgricultureIsNotIdenticalToSilviculture : SyntropicMeansSilviculturePermission → ⊥
syntropicAgricultureIsNotIdenticalToSilviculture ()

soilCarbonIncreaseDoesNotByItselfProveWholeFarmClimateBenefit :
  SoilCarbonMeansWholeFarmClimateBenefitPermission → ⊥
soilCarbonIncreaseDoesNotByItselfProveWholeFarmClimateBenefit ()

record SoilCarbonForestryBoundary : Set where
  constructor soil-carbon-forestry-boundary
  field
    soilCarbonNeedsDepthTimeBaselineAndMethod : Bool
    carbonStockAndCarbonFluxRemainDistinct : Bool
    silvicultureAndAgroforestryRemainDistinct : Bool
    conservationAgricultureIsMultiPrinciple : Bool
    regenerativeAgricultureDefinitionRemainsExplicit : Bool
    carbonOutcomeRequiresMeasurement : Bool

canonicalSoilCarbonForestryBoundary : SoilCarbonForestryBoundary
canonicalSoilCarbonForestryBoundary =
  soil-carbon-forestry-boundary true true true true true true
