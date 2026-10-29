module DASHI.Environment.RootSoilFungalIonWaterPhysiologyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Environment.FunctionalEcology as Ecology
import DASHI.Environment.LESFluidPhysicsCouplingExact as Fluid
import DASHI.Environment.QuantitiesConservation as Conservation
import DASHI.Environment.LESDomainBasisBidiFrontierExact as Basis
import DASHI.Physics.Electromagnetism.PoissonNernstPlanckElectrodiffusionExact as PNP
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Ernst Steudle,
-- "Water uptake by plant roots: an integration of views",
-- Plant and Soil 226 (2000), 45--56.
-- DOI: 10.1023/A:1026439226716.
--
-- Marie Barberon and Niko Geldner,
-- "Radial transport of nutrients: the plant root as a polarized epithelium",
-- Plant Physiology 166(2) (2014), 528--537.
-- DOI: 10.1104/pp.114.246124.
--
-- Sally E. Smith and F. Andrew Smith,
-- "Roles of Arbuscular Mycorrhizas in Plant Nutrition and Growth: New
-- Paradigms from Cellular to Ecosystem Scales",
-- Annual Review of Plant Biology 62 (2011), 227--250.
-- DOI: 10.1146/annurev-arplant-042110-103846.
--
-- SOURCE BOUNDARY
-- Steudle motivates composite radial root-water transport through apoplastic
-- and cellular pathways and its dependence on root hydraulic properties.
-- Barberon/Geldner motivate apoplastic, symplastic and trans-cellular nutrient
-- routes and the endodermal barrier. Smith/Smith motivate distinct direct-root
-- and arbuscular-mycorrhizal nutrient-acquisition pathways and their interplay.
--
-- The typed SI/PNP/fluid/chemistry/ecology/conservation composition below is a
-- DASHI reconstruction. It does not assert one constitutive parameterisation,
-- species list or hydraulic law for all roots, soils or fungal associations.
------------------------------------------------------------------------

data RootWaterPathway : Set where
  apoplasticWaterPathway : RootWaterPathway
  cellularWaterPathway : RootWaterPathway
  compositeRadialWaterPathway : RootWaterPathway

data RootNutrientPathway : Set where
  apoplasticNutrientPathway : RootNutrientPathway
  symplasticNutrientPathway : RootNutrientPathway
  transCellularNutrientPathway : RootNutrientPathway

data PlantNutrientAcquisitionPathway : Set where
  directRootPathway : PlantNutrientAcquisitionPathway
  mycorrhizalPathway : PlantNutrientAcquisitionPathway

directAndMycorrhizalPathwaysDistinct :
  directRootPathway ≡ mycorrhizalPathway → ⊥
directAndMycorrhizalPathwaysDistinct ()

------------------------------------------------------------------------
-- Root-water mechanics.
------------------------------------------------------------------------

record RootWaterTransportReceipt : Set₁ where
  constructor rootWaterTransportReceipt
  field
    RootWaterState : Set
    waterPotentialScale : SI.DecimalScale
    radialFluxScale : SI.DecimalScale

    soilWaterPotential : RootWaterState → SI.Quantity SI.Pressure waterPotentialScale
    rootWaterPotential : RootWaterState → SI.Quantity SI.Pressure waterPotentialScale
    radialWaterFluxDensity : RootWaterState → SI.Quantity SI.Velocity radialFluxScale

    pathway : RootWaterPathway
    fluidReduction : Fluid.FluidReductionReceipt
    rootGeometryReference : String
    hydraulicConductivityReference : String
    osmoticHydraulicDrivingReference : String
    aquaporinOrMembraneReference : String
    initialBoundaryConditionReference : String
    experimentalValidationReference : String

open RootWaterTransportReceipt public

------------------------------------------------------------------------
-- Direct soil -> root ion interface.
------------------------------------------------------------------------

record RootSoilIonInterface : Set₁ where
  constructor rootSoilIonInterface
  field
    soilPoreElectrodiffusion : PNP.ElectrodiffusionApplicationReceipt
    rootElectrodiffusion : PNP.ElectrodiffusionApplicationReceipt

    soilApplicationIsSoilPore :
      PNP.application soilPoreElectrodiffusion ≡ PNP.soilPoreElectrochemistry
    rootApplicationIsPlantRoot :
      PNP.application rootElectrodiffusion ≡ PNP.plantRootIonTransport

    sameIonicSpecies :
      PNP.species soilPoreElectrodiffusion
      ≡ PNP.species rootElectrodiffusion

    radialPathway : RootNutrientPathway
    soilRootInterfaceGeometryReference : String
    membraneCarrierSelectivityReference : String
    endodermalBarrierReference : String
    interfaceFluxOrientationReference : String
    interfaceFluxConservationReference : String
    validationReference : String

open RootSoilIonInterface public

------------------------------------------------------------------------
-- Water and ions need a literal common application state, not just parallel
-- records whose time/geometry happen to have similar labels.
------------------------------------------------------------------------

record RootWaterIonStateWeld
    (water : RootWaterTransportReceipt)
    (ions : RootSoilIonInterface) : Set₁ where
  constructor rootWaterIonStateWeld
  field
    CoupledState : Set
    waterState : CoupledState → RootWaterState water
    rootIonState :
      CoupledState →
      PNP.CoupledState (PNP.fluxLaw (rootElectrodiffusion ions))
    soilIonState :
      CoupledState →
      PNP.CoupledState (PNP.fluxLaw (soilPoreElectrodiffusion ions))

    commonGeometryReference : String
    commonTimeReference : String
    waterIonDrivingCouplingReference : String
    stateSynchronizationValidationReference : String

open RootWaterIonStateWeld public

------------------------------------------------------------------------
-- Root chemistry and conservation ledger.
------------------------------------------------------------------------

record RootSoilChemistryConservationWeld : Set₁ where
  constructor rootSoilChemistryConservationWeld
  field
    soilChemistry : Chemistry.ReactionNetwork
    rootChemistry : Chemistry.ReactionNetwork
    interfaceTransition : Chemistry.Transition
    balances : Conservation.ConservationBundle

    dissolvedSpeciesIdentificationReference : String
    chemistryToPNPSpeciesReference : String
    reactionSourceSinkReference : String
    waterBalanceCouplingReference : String
    nitrogenBalanceCouplingReference : String
    phosphorusBalanceCouplingReference : String
    carbonCostOrSupplyReference : String
    commonTimeSupportReference : String

open RootSoilChemistryConservationWeld public

------------------------------------------------------------------------
-- Base root-soil mechanism. Fungal symbiosis remains an extension because not
-- every plant/soil state should be silently classified as mycorrhizal.
------------------------------------------------------------------------

record RootSoilIonWaterMechanism : Set₁ where
  constructor rootSoilIonWaterMechanism
  field
    rootFunctionalGroup : Ecology.FunctionalGroup
    waterTransport : RootWaterTransportReceipt
    ionInterface : RootSoilIonInterface
    coupledWaterIonState : RootWaterIonStateWeld waterTransport ionInterface
    chemistryConservation : RootSoilChemistryConservationWeld

    rootAnatomyReference : String
    transporterOrChannelReference : String
    growthOrDemandCouplingReference : String
    scaleCompatibilityReference : String

open RootSoilIonWaterMechanism public

------------------------------------------------------------------------
-- Mycorrhizal extension.
------------------------------------------------------------------------

record MycorrhizalIonWaterExtension
    (base : RootSoilIonWaterMechanism) : Set₁ where
  constructor mycorrhizalIonWaterExtension
  field
    candidate : Ecology.MycorrhizalCandidate
    candidateAdmissible : Ecology.mycorrhizalCandidateAdmissible candidate ≡ true

    fungalElectrodiffusion : PNP.ElectrodiffusionApplicationReceipt
    fungalApplicationIsFungalExchange :
      PNP.application fungalElectrodiffusion ≡ PNP.fungalIonExchange

    sameRootTargetReference : String
    hostCompatibilityReference : String
    fungalSoilInterfaceReference : String
    fungalRootInterfaceReference : String
    phosphorusTransferReference : String
    nitrogenTransferReference : String
    plantCarbonCostReference : String
    directAndMycorrhizalPathwaySeparationReference : String
    fieldValidationReference : String

open MycorrhizalIonWaterExtension public

------------------------------------------------------------------------
-- Stage-7 realization seam.
------------------------------------------------------------------------

record RootSoilFungalDomainRealization : Set₁ where
  constructor rootSoilFungalDomainRealization
  field
    domainMechanism : Basis.DomainMechanismSocket
    rootSoilMechanism : RootSoilIonWaterMechanism
    mycorrhizalExtensions : List (MycorrhizalIonWaterExtension rootSoilMechanism)

    stateIdentificationReference : String
    controlIdentificationReference : String
    observationIdentificationReference : String
    discrepancyModelReference : String
    experimentDesignReference : String
    identifiabilityReference : String
    heldOutValidationReference : String

open RootSoilFungalDomainRealization public

steudleRootWaterDOI : String
steudleRootWaterDOI = "10.1023/A:1026439226716"

barberonGeldnerRootNutrientDOI : String
barberonGeldnerRootNutrientDOI = "10.1104/pp.114.246124"

smithSmithMycorrhizaDOI : String
smithSmithMycorrhizaDOI = "10.1146/annurev-arplant-042110-103846"

record RootSoilFungalPhysiologyBoundary : Set where
  constructor rootSoilFungalPhysiologyBoundary
  field
    pressureTypedWaterPotentialIsCompleteRootHydraulicModel : Bool
    pressureTypedWaterPotentialIsCompleteRootHydraulicModelIsFalse :
      pressureTypedWaterPotentialIsCompleteRootHydraulicModel ≡ false

    pnpIonTransportAloneIsCompletePlantNutrition : Bool
    pnpIonTransportAloneIsCompletePlantNutritionIsFalse :
      pnpIonTransportAloneIsCompletePlantNutrition ≡ false

    functionalRootRoleIsPlantPhysiology : Bool
    functionalRootRoleIsPlantPhysiologyIsFalse :
      functionalRootRoleIsPlantPhysiology ≡ false

    mycorrhizalCompatibilityProvesNutrientBenefit : Bool
    mycorrhizalCompatibilityProvesNutrientBenefitIsFalse :
      mycorrhizalCompatibilityProvesNutrientBenefit ≡ false

    plantTissueNutrientContentDeterminesMycorrhizalPathwayFlux : Bool
    plantTissueNutrientContentDeterminesMycorrhizalPathwayFluxIsFalse :
      plantTissueNutrientContentDeterminesMycorrhizalPathwayFlux ≡ false

    parallelWaterIonRecordsProveSameDynamicState : Bool
    parallelWaterIonRecordsProveSameDynamicStateIsFalse :
      parallelWaterIonRecordsProveSameDynamicState ≡ false

    rootSoilFungalMechanismNeedsSharedSpeciesAndConservationReceipts : Bool
    rootSoilFungalMechanismNeedsSharedSpeciesAndConservationReceiptsIsTrue :
      rootSoilFungalMechanismNeedsSharedSpeciesAndConservationReceipts ≡ true

    stage7PromotionStillNeedsExperimentsAndValidation : Bool
    stage7PromotionStillNeedsExperimentsAndValidationIsTrue :
      stage7PromotionStillNeedsExperimentsAndValidation ≡ true

open RootSoilFungalPhysiologyBoundary public

canonicalRootSoilFungalPhysiologyBoundary : RootSoilFungalPhysiologyBoundary
canonicalRootSoilFungalPhysiologyBoundary =
  rootSoilFungalPhysiologyBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl


------------------------------------------------------------------------
-- Spatial sentinel bioassay and soil-moisture nutrient-transport boundary.
--
-- PRIMARY SOURCES
--
-- Petra Marschner and Zed Rengel,
-- "Nutrient availability in soils", in Marschner's Mineral Nutrition of
-- Plants, 4th ed. (2023), pp. 499--522.
-- DOI: 10.1016/B978-0-12-819773-8.00003-4.
--
-- Agriculture Victoria, "Avoiding crop damage from residual herbicides".
-- NSW Government, "Herbicide residues".
-- Department of Primary Industries and Regional Development (WA),
-- "Residual herbicides - carryover and behaviour in dry conditions".
--
-- SOURCE BOUNDARY
-- The sources support soil-water control of nutrient mobility and the use of
-- controlled plant bioassays for residual-herbicide screening. The typed
-- diagnostic carrier below is DASHI reconstruction. A visible plant phenotype
-- remains an observation. It does not identify one chemical cause by itself.
------------------------------------------------------------------------

data IndicatorPhenotype : Set where
  interveinalChlorosis : IndicatorPhenotype
  paleOrLightVeins : IndicatorPhenotype
  reducedVigour : IndicatorPhenotype
  abnormalRootArchitecture : IndicatorPhenotype

data SoilStressHypothesis : Set where
  residualHerbicideCarryover : SoilStressHypothesis
  heavyMetalOrPaintResidue : SoilStressHypothesis
  pHAvailabilityShift : SoilStressHypothesis
  moistureLimitedNutrientTransport : SoilStressHypothesis
  waterloggingRootStress : SoilStressHypothesis
  salinityOrIonImbalance : SoilStressHypothesis

data PhenotypeCauseCompatibility : IndicatorPhenotype → SoilStressHypothesis → Set where
  chlorosisResidualHerbicideCandidate :
    PhenotypeCauseCompatibility interveinalChlorosis residualHerbicideCarryover
  chlorosisPHCandidate :
    PhenotypeCauseCompatibility interveinalChlorosis pHAvailabilityShift
  chlorosisMetalCandidate :
    PhenotypeCauseCompatibility interveinalChlorosis heavyMetalOrPaintResidue
  vigourMoistureCandidate :
    PhenotypeCauseCompatibility reducedVigour moistureLimitedNutrientTransport
  vigourWaterloggingCandidate :
    PhenotypeCauseCompatibility reducedVigour waterloggingRootStress

record UniqueCausePromotion (phenotype : IndicatorPhenotype) : Set where
  constructor uniqueCausePromotion
  field
    promotedCause : SoilStressHypothesis
    allCompatibleSame :
      ∀ {candidate} →
      PhenotypeCauseCompatibility phenotype candidate →
      candidate ≡ promotedCause

open UniqueCausePromotion public

interveinalChlorosisUniqueCausePromotionImpossible :
  UniqueCausePromotion interveinalChlorosis → ⊥
interveinalChlorosisUniqueCausePromotionImpossible promotion
  with allCompatibleSame promotion chlorosisResidualHerbicideCandidate
... | refl
  with allCompatibleSame promotion chlorosisPHCandidate
... | ()

record SpatialSentinelBioassayReceipt : Set where
  constructor spatialSentinelBioassayReceipt
  field
    sameIndicatorSpecies : Bool
    controlledSeedOrPropagationReference : String
    fixedOrRecordedSpacing : Bool
    suspectBoundaryRecorded : Bool
    comparisonAreaRecorded : Bool
    wateringSourceRecorded : Bool
    soilDepthRecorded : Bool
    moistureConditionRecorded : Bool
    phenotypeRecorded : Bool
    rootPhenotypeRecorded : Bool
    repeatedSpatialPatternRecorded : Bool
    laboratoryOrLabelFollowupReference : String
    controlSoilReference : String
    observationGeometryReference : String

open SpatialSentinelBioassayReceipt public

record SoilMoistureNutrientTransportBoundary : Set where
  constructor soilMoistureNutrientTransportBoundary
  field
    soilWaterParticipatesInDissolvedIonTransport : Bool
    massFlowAndDiffusionRemainDistinctTransportRoutes : Bool
    soilWaterContentCanChangeNutrientAvailability : Bool
    soilMoistureCanChangeResidualHerbicideAvailabilityOrBreakdown : Bool
    waterloggingCanConfoundPlantBioassay : Bool
    moistureAloneDeterminesPlantNutrientStatus : Bool
    phenotypeAloneIdentifiesUniqueChemicalCause : Bool
    spatialReplicationRaisesDiagnosticValue : Bool
    controlledComparisonIsRequiredForCausalPromotion : Bool

open SoilMoistureNutrientTransportBoundary public

canonicalSoilMoistureNutrientTransportBoundary :
  SoilMoistureNutrientTransportBoundary
canonicalSoilMoistureNutrientTransportBoundary =
  soilMoistureNutrientTransportBoundary
    true
    true
    true
    true
    true
    false
    false
    true
    true

soilWaterParticipatesInNutrientTransport :
  soilWaterParticipatesInDissolvedIonTransport
    canonicalSoilMoistureNutrientTransportBoundary
  ≡ true
soilWaterParticipatesInNutrientTransport = refl

soilMoistureDoesNotDetermineNutrientStatusAlone :
  moistureAloneDeterminesPlantNutrientStatus
    canonicalSoilMoistureNutrientTransportBoundary
  ≡ false
soilMoistureDoesNotDetermineNutrientStatusAlone = refl

plantPhenotypeDoesNotIdentifyUniqueChemicalCause :
  phenotypeAloneIdentifiesUniqueChemicalCause
    canonicalSoilMoistureNutrientTransportBoundary
  ≡ false
plantPhenotypeDoesNotIdentifyUniqueChemicalCause = refl

controlledComparisonRequiredBeforeCausalPromotion :
  controlledComparisonIsRequiredForCausalPromotion
    canonicalSoilMoistureNutrientTransportBoundary
  ≡ true
controlledComparisonRequiredBeforeCausalPromotion = refl

marschnerRengelNutrientAvailabilityDOI : String
marschnerRengelNutrientAvailabilityDOI =
  "10.1016/B978-0-12-819773-8.00003-4"
