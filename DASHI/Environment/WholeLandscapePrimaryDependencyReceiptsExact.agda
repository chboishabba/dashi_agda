module DASHI.Environment.WholeLandscapePrimaryDependencyReceiptsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Environment.WholeLandscapeSnowballDependencyFabricExact as Landscape
import DASHI.Environment.WholeLandscapePrimaryDependencySourceRegistryExact as Sources
import DASHI.Environment.NitrogenPathwayEnergeticMaterialComparisonExact as Nitrogen
import DASHI.Environment.AquaticLivingInfrastructureExact as Aquatic

------------------------------------------------------------------------
-- PRIMARY-SOURCE-BOUND DEPENDENCY RECEIPTS
--
-- Each receipt binds one exact external primary study to one bounded observed
-- dependency.  The generic cross-lane edge is DASHI-owned reconstruction.
-- Nothing here transports the primary result beyond its declared site,
-- intervention, organism, hydraulic geometry, time or consumer boundary.
------------------------------------------------------------------------

record FireToFuelPrimaryReceipt : Set where
  constructor fire-to-fuel-primary-receipt
  field
    source : Sources.PrimaryDependencySource
    sourceIsPrescribedFireFuelStudy :
      Sources.domain source ≡ Sources.fireToFuel
    exactExperimentalPlotReference : String
    exactBurnEventReference : String
    vegetationTypeReference : String
    climateZoneReference : String
    preFireFuelMeasurementReference : String
    postFireFuelMeasurementReference : String
    residualBiomassReference : String
    fireWeatherReference : String
    measuredFuelTransitionReference : String
    externalClaimOwner : Attribution.ClaimOwner
    externalOwnerIsSource :
      externalClaimOwner ≡ Attribution.externalSourceOwner

open FireToFuelPrimaryReceipt public

fireToFuelPrimaryEdge : FireToFuelPrimaryReceipt → Landscape.LandscapeDependencyEdge
fireToFuelPrimaryEdge receipt =
  Landscape.landscape-dependency-edge
    "primary-prescribed-fire-to-fuel-state"
    (Landscape.fireRegime ∷ [])
    (Landscape.fuel ∷ Landscape.carbon ∷ [])
    Landscape.ecologicalDependency
    Landscape.directMeasurementReceipt
    (FireToFuelPrimaryReceipt.exactExperimentalPlotReference receipt)
    (FireToFuelPrimaryReceipt.measuredFuelTransitionReference receipt)
    (FireToFuelPrimaryReceipt.preFireFuelMeasurementReference receipt)
    "external primary prescribed-fire study; DASHI edge reconstruction"
    []
    "Same experimental plot and burn event carry pre/post biomass-fuel observations."
    "Does not identify the measured fuel transition with universal wildfire-risk reduction, cultural burning efficacy, or transport to a different fuel complex."

record GrazingToFuelPrimaryReceipt : Set where
  constructor grazing-to-fuel-primary-receipt
  field
    source : Sources.PrimaryDependencySource
    sourceIsTargetedCattleFuelStudy :
      Sources.domain source ≡ Sources.grazingToFuel
    experimentalCommunityReference : String
    grazingTreatmentReference : String
    seasonReference : String
    utilizationReference : String
    shrubCoverReference : String
    preGrazingFuelReference : String
    postGrazingFuelReference : String
    fireBehaviourMeasurementReference : String
    samePlotTreatmentReference : String
    externalClaimOwner : Attribution.ClaimOwner
    externalOwnerIsSource :
      externalClaimOwner ≡ Attribution.externalSourceOwner

open GrazingToFuelPrimaryReceipt public

grazingToFuelPrimaryEdge : GrazingToFuelPrimaryReceipt → Landscape.LandscapeDependencyEdge
grazingToFuelPrimaryEdge receipt =
  Landscape.landscape-dependency-edge
    "primary-targeted-grazing-to-fuel-state"
    (Landscape.grazing ∷ [])
    (Landscape.fuel ∷ [])
    Landscape.ecologicalDependency
    Landscape.causalIdentificationReceipt
    (GrazingToFuelPrimaryReceipt.samePlotTreatmentReference receipt)
    (GrazingToFuelPrimaryReceipt.grazingTreatmentReference receipt)
    (GrazingToFuelPrimaryReceipt.postGrazingFuelReference receipt)
    "external replicated factorial cattle-grazing study; DASHI edge reconstruction"
    []
    "Replicated treatment structure directly links bounded grazing treatments to measured herbaceous fuel-state changes in the study system."
    "Does not generalise across herbivore species, shrub cover, vegetation types or climates, and does not identify fire-behaviour metrics with whole-wildfire risk."

record NitrogenToCropSoilPrimaryReceipt : Set where
  constructor nitrogen-to-crop-soil-primary-receipt
  field
    source : Sources.PrimaryDependencySource
    sourceIs15NTracerStudy :
      Sources.domain source ≡ Sources.nitrogenToCropSoil
    exactFieldReference : String
    exactCropReference : String
    fertiliserRateReference : String
    isotopeTracerReference : String
    fertiliserDerivedCropUptakeReference : String
    soilResidualNitrogenReference : String
    lossReference : String
    totalNitrogenPartitionReference : String
    timeHorizonReference : String
    externalClaimOwner : Attribution.ClaimOwner
    externalOwnerIsSource :
      externalClaimOwner ≡ Attribution.externalSourceOwner

open NitrogenToCropSoilPrimaryReceipt public

nitrogenToCropSoilPrimaryEdge :
  NitrogenToCropSoilPrimaryReceipt → Landscape.LandscapeDependencyEdge
nitrogenToCropSoilPrimaryEdge receipt =
  Landscape.landscape-dependency-edge
    "primary-15N-delivery-to-crop-soil-fate"
    (Landscape.nitrogen ∷ [])
    (Landscape.soil ∷ [])
    Landscape.conservationDependency
    Landscape.causalIdentificationReceipt
    (NitrogenToCropSoilPrimaryReceipt.exactFieldReference receipt)
    (NitrogenToCropSoilPrimaryReceipt.totalNitrogenPartitionReference receipt)
    (NitrogenToCropSoilPrimaryReceipt.soilResidualNitrogenReference receipt)
    "external primary 15N tracer study; DASHI edge reconstruction"
    []
    "The isotope tracer distinguishes fertilizer-derived crop uptake, soil residual and loss in the exact studied wheat-soil system; the whole-landscape edge targets the represented soil fate only."
    "Crop uptake remains in the exact tracer receipt until welded to the existing plant/SPAC owner; this does not transport fertilizer partitioning to PAW, compost, BNF, aquaponics, KNF, another crop or another site."

------------------------------------------------------------------------
-- Existing nitrogen packets may only use the primary tracer result as an
-- adjacent/transfer comparator unless the exact pathway/site/crop matches.
------------------------------------------------------------------------

record NitrogenPacketPrimaryComparison : Set where
  constructor nitrogen-packet-primary-comparison
  field
    packet : Nitrogen.NitrogenDeliveryPacket
    primaryReceipt : NitrogenToCropSoilPrimaryReceipt
    pathwayMatchReference : String
    cropMatchReference : String
    soilMatchReference : String
    climateMatchReference : String
    timingMatchReference : String
    fertiliserFormMatchReference : String
    directTransferPaymentAllowed : Bool

open NitrogenPacketPrimaryComparison public

record HydraulicHeadWaterServicePrimaryReceipt : Set where
  constructor hydraulic-head-water-service-primary-receipt
  field
    source : Sources.PrimaryDependencySource
    sourceIsGravityHeadStudy :
      Sources.domain source ≡ Sources.hydraulicHeadToWaterService
    exactSystemReference : String
    headReference : String
    slopeReference : String
    pipeEmitterGeometryReference : String
    measuredFlowReference : String
    coefficientUniformityReference : String
    emissionUniformityReference : String
    serviceBoundaryReference : String
    externalClaimOwner : Attribution.ClaimOwner
    externalOwnerIsSource :
      externalClaimOwner ≡ Attribution.externalSourceOwner

open HydraulicHeadWaterServicePrimaryReceipt public

hydraulicHeadWaterServicePrimaryEdge :
  HydraulicHeadWaterServicePrimaryReceipt → Landscape.LandscapeDependencyEdge
hydraulicHeadWaterServicePrimaryEdge receipt =
  Landscape.landscape-dependency-edge
    "primary-hydraulic-head-to-water-distribution-service"
    (Landscape.energy ∷ Landscape.infrastructure ∷ [])
    (Landscape.hydrology ∷ [])
    Landscape.hydraulicDependency
    Landscape.directMeasurementReceipt
    (HydraulicHeadWaterServicePrimaryReceipt.exactSystemReference receipt)
    (HydraulicHeadWaterServicePrimaryReceipt.headReference receipt)
    (HydraulicHeadWaterServicePrimaryReceipt.emissionUniformityReference receipt)
    "external primary gravity-fed hydraulic experiment; DASHI edge reconstruction"
    []
    "Hydraulic head and slope were experimentally varied and water-distribution uniformity measured in the declared gravity-fed drip geometry."
    "Does not prove pump displacement, lower lifecycle energy, aquaculture adequacy, crop benefit, or performance under different pipes, emitters, slopes or heads."

------------------------------------------------------------------------
-- Same-object weld into an actual DASHI hydraulic circuit remains separate.
------------------------------------------------------------------------

record HydraulicCircuitPrimaryWeld
    (receipt : HydraulicHeadWaterServicePrimaryReceipt)
    (circuit : Aquatic.HydraulicCircuit) : Set where
  constructor hydraulic-circuit-primary-weld
  field
    sameHeadReference : String
    sameGeometryReference : String
    sameFlowReference : String
    deliveredFlowMeasurementMatchesCircuit : String
    matchedServiceReference : String
    primaryStudyIsMechanismCalibrationNotSystemPerformanceTransfer : Bool

open HydraulicCircuitPrimaryWeld public

------------------------------------------------------------------------
-- Attribution / WrongType barriers.
------------------------------------------------------------------------

data PrimaryReceiptMeansUniversalEdgePermission : Set where
data DirectMeasurementMeansCausalUniversalityPermission : Set where
data FifteenNStudyMeansAllNitrogenPathwaysPermission : Set where
data GravityDripStudyMeansPumpDisplacementPermission : Set where
data FuelReductionMeansWildfireRiskReductionPermission : Set where
data DashiEdgeMeansExternalSourceClaimPermission : Set where

primaryReceiptDoesNotCreateUniversalEdge :
  PrimaryReceiptMeansUniversalEdgePermission → ⊥
primaryReceiptDoesNotCreateUniversalEdge ()

directMeasurementDoesNotCreateCausalUniversality :
  DirectMeasurementMeansCausalUniversalityPermission → ⊥
directMeasurementDoesNotCreateCausalUniversality ()

fifteenNStudyDoesNotPayAllNitrogenPathways :
  FifteenNStudyMeansAllNitrogenPathwaysPermission → ⊥
fifteenNStudyDoesNotPayAllNitrogenPathways ()

gravityStudyDoesNotProvePumpDisplacement :
  GravityDripStudyMeansPumpDisplacementPermission → ⊥
gravityStudyDoesNotProvePumpDisplacement ()

fuelReductionDoesNotByItselfProveWildfireRiskReduction :
  FuelReductionMeansWildfireRiskReductionPermission → ⊥
fuelReductionDoesNotByItselfProveWildfireRiskReduction ()

dashiDependencyDoesNotBecomeExternalSourceClaim :
  DashiEdgeMeansExternalSourceClaimPermission → ⊥
dashiDependencyDoesNotBecomeExternalSourceClaim ()

record WholeLandscapePrimaryReceiptBoundary : Set where
  constructor whole-landscape-primary-receipt-boundary
  field
    exactSourceExperimentAndGenericDependencyRemainDistinct : Bool
    directMeasurementAndTransportRemainDistinct : Bool
    primarySourceOwnerRemainsExternal : Bool
    dashiDependencyWeldRemainsDashiOwned : Bool
    exactSiteAndSystemIdentityRequiredForDirectPayment : Bool
    primaryStudyAutomaticallyPaysRecommendation : Bool

canonicalWholeLandscapePrimaryReceiptBoundary : WholeLandscapePrimaryReceiptBoundary
canonicalWholeLandscapePrimaryReceiptBoundary =
  whole-landscape-primary-receipt-boundary true true true true true false
