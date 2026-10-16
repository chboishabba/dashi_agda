module DASHI.Physics.Plasma.FusionPropulsionLiteralMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.MagneticConfinementMachineExact as Confinement
import DASHI.Physics.Plasma.FRCCompressionFusionHyperfabricExact as LegacyFRC
import DASHI.Physics.Plasma.MagneticNozzleMomentumConversionBidiExact as LegacyNozzle
import DASHI.Physics.Plasma.FusionPropulsionScienceBidiCrossPollinationExact as LegacyChain

------------------------------------------------------------------------
-- EVIDENCE AND ATTRIBUTION FIREWALL
--
-- The constructors are intentionally disjoint.  A paper's claim kind cannot
-- silently become an experimental observation, and a planned measurement or
-- company statement cannot enter quantitative calibration.
------------------------------------------------------------------------

data EvidenceClass : Set where
  measuredObservation : EvidenceClass
  simulationToExperimentComparison : EvidenceClass
  analyticOrKineticTheory : EvidenceClass
  plannedMeasurement : EvidenceClass
  companyClaim : EvidenceClass

record SourceAttribution : Set where
  constructor source-attribution
  field
    evidenceClass : EvidenceClass
    title : String
    locator : String
    publicationDate : String
    independentReproductionIdentified : Bool

open SourceAttribution public

data CalibrationAuthority : EvidenceClass → Set where
  measured-calibration : CalibrationAuthority measuredObservation
  simulation-validation-target :
    CalibrationAuthority simulationToExperimentComparison
  theory-validation-target : CalibrationAuthority analyticOrKineticTheory

record QuantitativeClaim (A : Set) : Set₁ where
  constructor quantitative-claim
  field
    value : A
    claimSource : SourceAttribution
    calibrationAuthority : CalibrationAuthority (evidenceClass claimSource)
    uncertainty : Set
    uncertaintyReceipt : uncertainty

open QuantitativeClaim public

qinfischRootPoleSource : SourceAttribution
qinfischRootPoleSource =
  source-attribution
    analyticOrKineticTheory
    "Energetic-ion root-pole coupling to an ion-Bernstein-wave root"
    "https://arxiv.org/abs/2609.07732"
    "2026-09-17"
    false

zhuWuYingguang1Source : SourceAttribution
zhuWuYingguang1Source =
  source-attribution
    simulationToExperimentComparison
    "Whole-device three-dimensional kinetic FRC formation for Yingguang-1"
    "https://arxiv.org/abs/2607.11908"
    "2026-07-02"
    false

rikenPB11TargetSource : SourceAttribution
rikenPB11TargetSource =
  source-attribution
    plannedMeasurement
    "Thin self-supporting enriched boron-11 target development"
    "https://indico2.riken.jp/event/5355/contributions/28952/"
    "2026-09-04"
    false

americanFusionClaimSource : SourceAttribution
americanFusionClaimSource =
  source-attribution
    companyClaim
    "American Fusion pulsed-field configuration statement"
    "https://finance.yahoo.com/energy/articles/american-fusion-texatron-testing-results-144825138.html"
    "2026-09-15"
    false

------------------------------------------------------------------------
-- A. TIME-DEPENDENT WHOLE-DEVICE FRC FORMATION
------------------------------------------------------------------------

record KineticElectronIonState : Set₁ where
  constructor kinetic-electron-ion-state
  field
    ElectronDistribution IonDistribution : Set
    electronDistribution : ElectronDistribution
    ionDistribution : IonDistribution
    electronTemperature ionTemperature : Set
    electronTemperatureValue : electronTemperature
    ionTemperatureValue : ionTemperature

open KineticElectronIonState public

record CircuitPlasmaCoupling : Set₁ where
  constructor circuit-plasma-coupling
  field
    ElectricField MagneticField CoilCurrent CircuitVoltage : Set
    electricField : ElectricField
    magneticField : MagneticField
    coilCurrent : CoilCurrent
    circuitVoltage : CircuitVoltage
    embeddedPhysicalCoils : Bool
    embeddedPhysicalCoilsIsTrue : embeddedPhysicalCoils ≡ true
    externalCircuitDynamical : Bool
    externalCircuitDynamicalIsTrue : externalCircuitDynamical ≡ true
    couplingLawReceipt : Set

open CircuitPlasmaCoupling public

record SeparatrixTopology : Set₁ where
  constructor separatrix-topology
  field
    Separatrix : Set
    boundary : Separatrix
    closedPoloidalFluxReceipt : Set
    fieldReversalReceipt : Set

open SeparatrixTopology public

record NonAxisymmetricModeSpectrum : Set₁ where
  constructor non-axisymmetric-mode-spectrum
  field
    ModeNumber ModeAmplitude : Set
    m : ModeNumber
    amplitude : ModeAmplitude
    squareM4MorphologyReceipt : Set

open NonAxisymmetricModeSpectrum public

record LiteralFRCFormationState : Set₁ where
  constructor literal-frc-formation-state
  field
    kinetic : KineticElectronIonState
    circuitPlasma : CircuitPlasmaCoupling
    separatrix : SeparatrixTopology
    modes : NonAxisymmetricModeSpectrum
    legacyTopologyState : LegacyFRC.FRCState

open LiteralFRCFormationState public

record LiteralFRCFormationTrajectory : Set₁ where
  constructor literal-frc-formation-trajectory
  field
    Time : Set
    state : Time → LiteralFRCFormationState
    sameDeviceAcrossTime : Set
    formationLawReceipt : Set
    formationInitialValueReceipt : Set
    conductorBoundaryReceipt : Set

open LiteralFRCFormationTrajectory public

record FRCValidationVector (trajectory : LiteralFRCFormationTrajectory) : Set₁ where
  constructor frc-validation-vector
  field
    PeakIonDensity ElectronTemperature IonTemperature : Set
    SeparatrixRadius ReconnectionTime M4Amplitude : Set

    peakIonDensity : PeakIonDensity
    electronTemperature : ElectronTemperature
    ionTemperature : IonTemperature
    separatrixRadius : SeparatrixRadius
    reconnectionTime : ReconnectionTime
    m4Amplitude : M4Amplitude

    simultaneousSameTrajectoryReceipt : Set
    declaredToleranceReceipt : Set
    densityObservationComparison : QuantitativeClaim PeakIonDensity
    morphologyObservationComparison : QuantitativeClaim M4Amplitude
    kineticPredictionComparison : QuantitativeClaim ElectronTemperature
    ionPredictionComparison : QuantitativeClaim IonTemperature
    separatrixPredictionComparison : QuantitativeClaim SeparatrixRadius

open FRCValidationVector public

record EquilibriumReconstructionBoundary
  (trajectory : LiteralFRCFormationTrajectory) : Set₁ where
  constructor equilibrium-reconstruction-boundary
  field
    reconstructedState : Confinement.MagneticConfinementState
    lateTimeApproximation : Bool
    lateTimeApproximationIsTrue : lateTimeApproximation ≡ true
    reconstructionError : Set
    reconstructionErrorBoundReceipt : Set
    reconstructionDefinesFormedState : Bool
    reconstructionDefinesFormedStateIsFalse :
      reconstructionDefinesFormedState ≡ false

------------------------------------------------------------------------
-- B. ENERGETIC-ION / ION-BERNSTEIN ROOT-POLE CHANNEL
------------------------------------------------------------------------

record ThermalIBWRoot : Set₁ where
  constructor thermal-ibw-root
  field
    Frequency PerpendicularWaveNumber : Set
    rootFrequency : Frequency
    perpendicularWaveNumber : PerpendicularWaveNumber
    thermalDispersionVanishesReceipt : Set
    stableWithoutEnergeticIonsReceipt : Set

open ThermalIBWRoot public

record EnergeticIonCyclotronPole : Set₁ where
  constructor energetic-ion-cyclotron-pole
  field
    Frequency MinorityDensity Residue : Set
    poleFrequency : Frequency
    minorityDensity : MinorityDensity
    residue : Residue
    susceptibilityPoleReceipt : Set

open EnergeticIonCyclotronPole public

record RootPoleIdealRegime : Set where
  constructor root-pole-ideal-regime
  field
    homogeneous : Bool
    homogeneousIsTrue : homogeneous ≡ true
    collisionless : Bool
    collisionlessIsTrue : collisionless ≡ true
    parallelWaveNumberZero : Bool
    parallelWaveNumberZeroIsTrue : parallelWaveNumberZero ≡ true
    coldRing : Bool
    coldRingIsTrue : coldRing ≡ true
    exactNoncommensurateResonance : Bool
    exactNoncommensurateResonanceIsTrue :
      exactNoncommensurateResonance ≡ true

record RootPoleInstabilityReceipt
  (root : ThermalIBWRoot)
  (pole : EnergeticIonCyclotronPole) : Set₁ where
  constructor root-pole-instability-receipt
  field
    regime : RootPoleIdealRegime
    sameFrequencyReceipt : Set
    PositiveMinorityDensity : Set
    ComplexConjugateGrowingPair : Set
    anyPositiveDensityProducesPair :
      PositiveMinorityDensity → ComplexConjugateGrowingPair
    GrowthCoefficient SquareRootGrowthRemainder : Set
    squareRootGrowthReceipt : Set

open RootPoleInstabilityReceipt public

record RootPolePerturbationEnvelope : Set₁ where
  constructor root-pole-perturbation-envelope
  field
    Detuning RingWidth CollisionRate ParallelWaveNumber : Set
    GradientScale CompetingDamping SaturationAmplitude : Set
    detuning : Detuning
    ringWidth : RingWidth
    collisionRate : CollisionRate
    parallelWaveNumber : ParallelWaveNumber
    gradientScale : GradientScale
    competingDamping : CompetingDamping
    saturationAmplitude : SaturationAmplitude
    stabilityOrInstabilityRegionReceipt : Set
    exactResonanceResultTransferredAutomatically : Bool
    exactResonanceResultTransferredAutomaticallyIsFalse :
      exactResonanceResultTransferredAutomatically ≡ false

record SpeciesResolvedPowerTransfer : Set₁ where
  constructor species-resolved-power-transfer
  field
    FusionProductSpecies ThermalSpecies Power : Set
    sourceSpecies : FusionProductSpecies
    recipientSpecies : ThermalSpecies
    productPowerLoss coherentThermalResponsePower : Power
    powerPartitionReceipt : Set
    transferSource : SourceAttribution

open SpeciesResolvedPowerTransfer public

------------------------------------------------------------------------
-- C. UNCERTAINTY-BEARING FUEL CYCLES AND SAME-STATE POWER BALANCE
------------------------------------------------------------------------

data FuelCycle : Set where
  deuteriumHelium3 : FuelCycle
  protonBoron11 : FuelCycle

record CrossSectionNuisanceParameters : Set₁ where
  constructor cross-section-nuisance-parameters
  field
    TargetThickness Enrichment StoppingPower DetectorSolidAngle : Set
    AlphaBranchReconstruction EnergyCalibration : Set
    targetThickness : TargetThickness
    enrichment : Enrichment
    stoppingPower : StoppingPower
    detectorSolidAngle : DetectorSolidAngle
    alphaBranchReconstruction : AlphaBranchReconstruction
    energyCalibration : EnergyCalibration

record CrossSectionModelFamily : Set₁ where
  constructor cross-section-model-family
  field
    Energy Parameter CrossSection : Set
    sigma : Energy → Parameter → CrossSection
    competingDataSets : Set
    posteriorOrAdmissibleFamilyReceipt : Set
    nuisance : CrossSectionNuisanceParameters
    canonicalCurveIsExact : Bool
    canonicalCurveIsExactIsFalse : canonicalCurveIsExact ≡ false

open CrossSectionModelFamily public

record DistributionDependentBurn
  (fuel : FuelCycle)
  (formation : LiteralFRCFormationTrajectory) : Set₁ where
  constructor distribution-dependent-burn
  field
    Reactivity ChargedProductDistribution : Set
    SecondaryNeutronSpectrum LossPower UsefulPower : Set
    reactivity : Reactivity
    chargedProducts : ChargedProductDistribution
    secondaryNeutrons : SecondaryNeutronSpectrum
    bremsstrahlung synchrotron transportLoss sustainPower : LossPower
    conversionLoss productEscape ashRemoval : LossPower
    usefulPower : UsefulPower
    crossSections : CrossSectionModelFamily
    distributionIntegralReceipt : Set
    productSlowingDownReceipt : Set
    confinementReceipt : Set
    sameFormationStatePowerBalanceReceipt : Set
    netUsefulPowerPositiveReceipt : Set

open DistributionDependentBurn public

------------------------------------------------------------------------
-- D. SAME-OBJECT KINETIC PRODUCT CHANNEL AND SOLVED NOZZLE
------------------------------------------------------------------------

record ChargedProductKineticChannel
  {fuel : FuelCycle}
  {formation : LiteralFRCFormationTrajectory}
  (burn : DistributionDependentBurn fuel formation) : Set₁ where
  constructor charged-product-kinetic-channel
  field
    root : ThermalIBWRoot
    pole : EnergeticIonCyclotronPole
    idealInstability : RootPoleInstabilityReceipt root pole
    perturbations : RootPolePerturbationEnvelope
    transfer : SpeciesResolvedPowerTransfer
    BulkIonDistribution : Set
    bulkIonDistribution : BulkIonDistribution
    burnProductsArePolePopulationReceipt : Set
    transferProducesBulkDistributionReceipt : Set
    sameObjectAcrossBurnAndChannelReceipt : Set

open ChargedProductKineticChannel public

record SolvedMagneticNozzle
  {fuel : FuelCycle}
  {formation : LiteralFRCFormationTrajectory}
  {burn : DistributionDependentBurn fuel formation}
  (channel : ChargedProductKineticChannel burn) : Set₁ where
  constructor solved-magnetic-nozzle
  field
    Geometry ExitDistribution Thrust SpecificImpulse Efficiency : Set
    StressTensor AmbipolarPotential CoilReactionForce : Set
    geometry : Geometry
    exitDistribution : ExitDistribution
    thrust : Thrust
    specificImpulse : SpecificImpulse
    efficiency : Efficiency
    stressTensor : StressTensor
    ambipolarPotential : AmbipolarPotential
    coilReactionForce : CoilReactionForce
    finiteLarmorRadiusReceipt : Set
    detachmentReceipt : Set
    divergenceLossReceipt : Set
    wallInterceptionReceipt : Set
    momentumFluxIntegralReceipt : Set
    channelDistributionIsNozzleUpstreamReceipt : Set
    momentumConservationWithCoilsReceipt : Set
    legacyNozzleState : LegacyNozzle.NozzlePlasmaState
    legacyNozzleGeometry : LegacyNozzle.MagneticNozzleGeometry
    legacyThrustReceipt :
      LegacyNozzle.ThrustReceipt legacyNozzleState legacyNozzleGeometry

open SolvedMagneticNozzle public

------------------------------------------------------------------------
-- E. VEHICLE CLOSURE
------------------------------------------------------------------------

record EngineMassLedger : Set₁ where
  constructor engine-mass-ledger
  field
    Mass : Set
    magnetsAndCryogenics : Mass
    powerConditioningAndCurrentDrive : Mass
    radiationShielding : Mass
    plasmaFacingStructures : Mass
    thermalRejection : Mass
    propellantAndFuelInventory : Mass
    nozzleCoils : Mass
    structuralReactionLoads : Mass
    maintenanceMargin : Mass
    totalMassReceipt : Set

record VehicleClosure
  {fuel : FuelCycle}
  {formation : LiteralFRCFormationTrajectory}
  {burn : DistributionDependentBurn fuel formation}
  {channel : ChargedProductKineticChannel burn}
  (nozzle : SolvedMagneticNozzle channel) : Set₁ where
  constructor vehicle-closure
  field
    MassFlow ExhaustVelocity JetPower SystemPower SpecificPower : Set
    massFlow : MassFlow
    exhaustVelocity : ExhaustVelocity
    jetPower : JetPower
    systemPower : SystemPower
    specificPower : SpecificPower
    massLedger : EngineMassLedger
    jetPowerIdentityReceipt : Set
    thrustIdentityReceipt : Set
    specificImpulseIdentityReceipt : Set
    specificPowerIdentityReceipt : Set
    thermalClosureReceipt : Set
    missionPerformanceReceipt : Set
    nozzleThrustIsVehicleThrustReceipt : Set

open VehicleClosure public

------------------------------------------------------------------------
-- F. TERMINAL INHABITANT: ALL LINKS SHARE THE SAME INDEXED OBJECTS.
--
-- This constructor does not manufacture missing evidence.  It makes the exact
-- evidence package required to inhabit the terminal type explicit.
------------------------------------------------------------------------

record CompleteFusionPropulsionEvidencePackage : Set₁ where
  constructor complete-fusion-propulsion-evidence-package
  field
    fuel : FuelCycle
    formation : LiteralFRCFormationTrajectory
    validation : FRCValidationVector formation
    burn : DistributionDependentBurn fuel formation
    channel : ChargedProductKineticChannel burn
    nozzle : SolvedMagneticNozzle channel
    vehicle : VehicleClosure nozzle
    legacyChain : LegacyChain.FusionPropulsionScienceChain

    legacyFRCStateIsTrajectoryTerminalStateReceipt : Set
    legacyFusionIsBurnReceipt : Set
    legacyNozzleIsSolvedNozzleReceipt : Set
    legacyStringReferencesReplacedByTypedReceipts : Set

open CompleteFusionPropulsionEvidencePackage public

record LiteralDirectFusionDrive : Set₁ where
  constructor literal-direct-fusion-drive
  field
    evidence : CompleteFusionPropulsionEvidencePackage
    samePhysicalSystemReceipt : Set
    noAttributionUpgradeReceipt : Set
    quantitativeUncertaintyPropagatedReceipt : Set
    measuredThrustIfClaimedReceipt : Set

open LiteralDirectFusionDrive public

literalDirectFusionDrive :
  (package : CompleteFusionPropulsionEvidencePackage) →
  (samePhysicalSystemReceipt : Set) →
  (noAttributionUpgradeReceipt : Set) →
  (quantitativeUncertaintyPropagatedReceipt : Set) →
  (measuredThrustIfClaimedReceipt : Set) →
  LiteralDirectFusionDrive
literalDirectFusionDrive =
  literal-direct-fusion-drive

------------------------------------------------------------------------
-- CROSS-POLLINATION BOUNDARY
------------------------------------------------------------------------

record FusionPropulsionMaxCutBoundary : Set where
  constructor fusion-propulsion-max-cut-boundary
  field
    genericConfinementInterfacesReusable : Bool
    genericConfinementInterfacesReusableIsTrue :
      genericConfinementInterfacesReusable ≡ true

    tokamakOrStellaratorPerformanceTransfersToFRC : Bool
    tokamakOrStellaratorPerformanceTransfersToFRCIsFalse :
      tokamakOrStellaratorPerformanceTransfersToFRC ≡ false

    exactRootPoleResultTransfersToPerturbedRegimes : Bool
    exactRootPoleResultTransfersToPerturbedRegimesIsFalse :
      exactRootPoleResultTransfersToPerturbedRegimes ≡ false

    plannedPB11MeasurementUpdatesReactionRateNow : Bool
    plannedPB11MeasurementUpdatesReactionRateNowIsFalse :
      plannedPB11MeasurementUpdatesReactionRateNow ≡ false

    companyClaimCalibratesQuantitativeModel : Bool
    companyClaimCalibratesQuantitativeModelIsFalse :
      companyClaimCalibratesQuantitativeModel ≡ false

    chemicalRocketMaterialQualificationTransfersToFusionPlasma : Bool
    chemicalRocketMaterialQualificationTransfersToFusionPlasmaIsFalse :
      chemicalRocketMaterialQualificationTransfersToFusionPlasma ≡ false

    dimensionedQualificationMethodologyReusable : Bool
    dimensionedQualificationMethodologyReusableIsTrue :
      dimensionedQualificationMethodologyReusable ≡ true

canonicalFusionPropulsionMaxCutBoundary : FusionPropulsionMaxCutBoundary
canonicalFusionPropulsionMaxCutBoundary =
  fusion-propulsion-max-cut-boundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
