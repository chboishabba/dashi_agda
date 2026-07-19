module DASHI.Physics.Laws.PhysicalLawRecoveryBoundary where

open import Agda.Builtin.List using (List)

import DASHI.Physics.Laws.PhysicalLawCore as Core
import DASHI.Physics.Laws.PhysicalLawAtlas as Atlas
import DASHI.Physics.Laws.SpacetimeMechanicsLaws as Mechanics
import DASHI.Physics.Laws.QuantumFieldLaws as Quantum
import DASHI.Physics.Laws.GaugeInteractionLaws as Gauge
import DASHI.Physics.Laws.GravityCosmologyLaws as Gravity
import DASHI.Physics.Laws.ThermodynamicStatisticalLaws as Thermo
import DASHI.Physics.Laws.ContinuumMaterialLaws as Continuum
import DASHI.Physics.Laws.StandardModelLawBoundary as SM
import DASHI.Physics.Laws.ConstantsMetrologyBoundary as Metrology
import DASHI.Physics.Laws.EffectiveLimitHierarchy as Limits
import DASHI.Physics.Laws.ExistingPhysicsAdapter as Existing
import DASHI.Physics.Chemistry.AtomicPeriodicTableRecoveryBoundary as Atomic

-- Full physical-law dependency tower.  It assembles law classes and existing
-- DASHI proof/status lanes while keeping mathematical theorem, effective model,
-- empirical calibration, and open-problem authority distinct.
record PhysicalLawRecoveryBoundary : Setω where
  field
    lawAtlas : List Atlas.CanonicalPhysicalLaw
    existingPhysics : Existing.ExistingPhysicsAdapter

    spacetimeKinematics : Mechanics.SpacetimeKinematics
    differentialGeometry : Mechanics.DifferentialGeometricDynamics
    variationalMechanics : Mechanics.VariationalMechanics
    hamiltonianMechanics : Mechanics.HamiltonianMechanics
    noetherBridge        : Mechanics.NoetherLaw

    quantumKinematics : Quantum.QuantumKinematics
    quantumDynamics   : Quantum.QuantumDynamics quantumKinematics
    quantumMeasurement : Quantum.QuantumMeasurement quantumKinematics
    relativisticQFT    : Quantum.RelativisticQuantumField
    algebraicQFT       : Quantum.AlgebraicQFTLaw

    gaugeGeometry      : Gauge.GaugeFieldGeometry
    maxwellLaw         : Gauge.MaxwellFieldLaw
    yangMillsLaw       : Gauge.YangMillsFieldLaw
    interactionSectors : Gauge.InteractionSectorSystem

    gravityLaw         : Gravity.EinsteinGravityLaw
    cosmologyLaw       : Gravity.CosmologicalDynamics

    thermodynamicState : Thermo.ThermodynamicStateSpace
    zerothLaw          : Thermo.ZerothLaw thermodynamicState
    firstLaw           : Thermo.FirstLaw thermodynamicState
    secondLaw          : Thermo.SecondLaw thermodynamicState
    thirdLaw           : Thermo.ThirdLaw thermodynamicState
    statisticalEnsemble : Thermo.StatisticalEnsemble

    continuumBalance   : Continuum.ContinuumBalanceSystem
    constitutiveClosure : Continuum.ConstitutiveClosure
    elasticityLaw      : Continuum.ElasticityLaw
    fluidLaw           : Continuum.FluidDynamicsLaw
    diffusionLaw       : Continuum.DiffusionTransportLaw
    reactionDiffusion  : Continuum.ReactionDiffusionLaw
    plasmaLaw          : Continuum.PlasmaMagnetofluidLaw
    waveLaw            : Continuum.WaveOpticsAcousticsLaw

    standardModelLaw   : SM.StandardModelLawSurface
    metrologySystem    : Metrology.DimensionalQuantitySystem
    constantRegistry   : Metrology.PhysicalConstantRegistry
    calibrationChain   : Metrology.CalibrationChain
    renormalisationGroup : Limits.RenormalisationGroupLaw
    continuumLimit     : Limits.ContinuumLimitBoundary
    effectiveFieldTheory : Limits.EffectiveFieldTheoryLaw

    atomicChemistry    : Atomic.AtomicPeriodicTableRecoveryBoundary

    GeometryToMechanics : Set
    MechanicsToQuantum : Set
    GeometryToGaugeFields : Set
    GaugeMatterToStandardModel : Set
    GeometryMatterToGravity : Set
    MicroscopicToStatistical : Set
    StatisticalToThermodynamic : Set
    BalanceToConstitutiveContinuum : Set
    DiscreteToContinuum : Set
    QuantumToClassical : Set
    RelativisticToNewtonian : Set
    FieldsToAtomicChemistry : Set

    geometryMechanicsWitness : GeometryToMechanics
    mechanicsQuantumWitness : MechanicsToQuantum
    geometryGaugeWitness : GeometryToGaugeFields
    gaugeMatterSMWitness : GaugeMatterToStandardModel
    gravityCouplingWitness : GeometryMatterToGravity
    microStatisticalWitness : MicroscopicToStatistical
    statisticalThermoWitness : StatisticalToThermodynamic
    continuumClosureWitness : BalanceToConstitutiveContinuum
    discreteContinuumWitness : DiscreteToContinuum
    quantumClassicalWitness : QuantumToClassical
    relativisticNewtonianWitness : RelativisticToNewtonian
    fieldsAtomicWitness : FieldsToAtomicChemistry

record PhysicalLawRecoveryWitness
  (P : PhysicalLawRecoveryBoundary) : Setω where
  field
    KinematicsRecovered : Set
    ClassicalMechanicsRecovered : Set
    QuantumMechanicsRecovered : Set
    GaugeFieldLawsRecovered : Set
    GeneralRelativityRecovered : Set
    ThermodynamicStatisticalRecovery : Set
    ContinuumMaterialRecovery : Set
    StandardModelScopedRecovery : Set
    ConstantsAndMetrologyBound : Set
    EffectiveLimitMapsRecovered : Set
    AtomicChemistryRecovered : Set

    kinematicsWitness : KinematicsRecovered
    classicalMechanicsWitness : ClassicalMechanicsRecovered
    quantumMechanicsWitness : QuantumMechanicsRecovered
    gaugeWitness : GaugeFieldLawsRecovered
    gravityWitness : GeneralRelativityRecovered
    thermoWitness : ThermodynamicStatisticalRecovery
    continuumWitness : ContinuumMaterialRecovery
    standardModelWitness : StandardModelScopedRecovery
    metrologyWitness : ConstantsAndMetrologyBound
    limitsWitness : EffectiveLimitMapsRecovered
    atomicWitness : AtomicChemistryRecovered

-- These are the principal theorem/calibration blockers before a broad
-- first-principles recovery claim could be promoted.
record PhysicalLawOpenObligations
  (P : PhysicalLawRecoveryBoundary) : Setω where
  field
    differentialGeometryConcreteAdapters : Set
    actionHamiltonianLegendreAndNoetherRegularity : Set
    physicalHilbertSpaceAndSelfAdjointDomains : Set
    bornMeasurementAndEmpiricalProbabilityBridge : Set
    concreteInteractingAQFTOrWightmanModel : Set
    maxwellHodgeSourceCurrentAndUnitCalibration : Set
    yangMillsContinuumConstructionAndMassGap : Set
    standardModelContinuousUniquenessAndParameters : Set
    generalRelativityContinuumAndInitialValueControl : Set
    quantumGravityBridge : Set
    statisticalMeasureErgodicAndThermodynamicLimits : Set
    constitutiveMaterialCalibration : Set
    navierStokesThreeDimensionalRegularity : Set
    kineticFluidAndPlasmaLimitControl : Set
    uniformDiscreteContinuumConvergence : Set
    quantumClassicalCorrespondenceBounds : Set
    renormalisationUniversalityAndSchemeControl : Set
    versionedConstantsUnitsAndExperimentalAuthority : Set
    atomicManyBodyToChemistryRecovery : Set

-- "All physical laws" is an extensible coverage target, not a closed-world
-- theorem that no future or domain-specific law exists.
record PhysicalLawCoverageBoundary : Set₁ where
  field
    atlasCoversCanonicalFamilies : Set
    atlasIsExtensible            : Set
    domainSpecificConstitutiveLawsRemainOpen : Set
    newEmpiricalPhysicsCanExtendAtlas : Set
    equivalentFormulationsRequireBridgeProof : Set
    physicalTruthIsNotCreatedByEnumeration : Set

-- Open millennium and foundational problems remain explicit statuses.
data PhysicalLawPromotionStatus : Set where
  structuredLawAtlasPresent : PhysicalLawPromotionStatus
  scopedRecoveryOnly : PhysicalLawPromotionStatus
  empiricalAuthorityRequired : PhysicalLawPromotionStatus
  yangMillsMassGapOpen : PhysicalLawPromotionStatus
  navierStokesRegularityOpen : PhysicalLawPromotionStatus
  quantumGravityOpen : PhysicalLawPromotionStatus
  standardModelFirstPrinciplesOpen : PhysicalLawPromotionStatus
  universalTheoryNotPromoted : PhysicalLawPromotionStatus

physicalLawRecoveryAvailable :
  {P : PhysicalLawRecoveryBoundary} →
  PhysicalLawRecoveryWitness P → PhysicalLawRecoveryWitness P
physicalLawRecoveryAvailable witness = witness
