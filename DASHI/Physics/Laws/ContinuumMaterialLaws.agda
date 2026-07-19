module DASHI.Physics.Laws.ContinuumMaterialLaws where

-- Continuum equations combine balance laws with constitutive closures.  The
-- balances can be universal at the selected continuum scale while stress,
-- viscosity, diffusion, heat flux, reaction, and material response remain
-- model- and regime-dependent.
record ContinuumBalanceSystem : Set₁ where
  field
    DomainPoint : Set
    Time        : Set
    Density     : Set
    Velocity    : Set
    Momentum    : Set
    Energy      : Set
    Source      : Set
    Flux        : Set

    density     : Time → DomainPoint → Density
    velocity    : Time → DomainPoint → Velocity
    momentum    : Time → DomainPoint → Momentum
    energy      : Time → DomainPoint → Energy

    massFlux    : Time → DomainPoint → Flux
    momentumFlux : Time → DomainPoint → Flux
    energyFlux  : Time → DomainPoint → Flux

    massSource     : Time → DomainPoint → Source
    momentumSource : Time → DomainPoint → Source
    energySource   : Time → DomainPoint → Source

    massBalance     : Set
    momentumBalance : Set
    energyBalance   : Set

record ConstitutiveClosure : Set₁ where
  field
    StateVariable : Set
    Gradient      : Set
    Flux          : Set
    Stress        : Set
    MaterialParameter : Set

    constitutiveFlux : MaterialParameter → StateVariable → Gradient → Flux
    constitutiveStress : MaterialParameter → StateVariable → Gradient → Stress
    ValidState : MaterialParameter → StateVariable → Set
    FrameIndifferent : MaterialParameter → Set
    Dissipative      : MaterialParameter → Set

record ElasticityLaw : Set₁ where
  field
    ReferenceConfiguration : Set
    Deformation            : Set
    Strain                 : Set
    Stress                 : Set
    ElasticModulus         : Set
    EnergyDensity          : Set

    strainOf       : Deformation → Strain
    stressResponse : ElasticModulus → Strain → Stress
    storedEnergy   : ElasticModulus → Strain → EnergyDensity
    Equilibrium    : Deformation → Set
    StableMaterial : ElasticModulus → Set

record FluidDynamicsLaw : Set₁ where
  field
    FlowState    : Set
    Pressure     : Set
    Viscosity    : Set
    Force        : Set
    Time         : Set
    Domain       : Set

    velocity     : FlowState → Time → Domain → Set
    pressure     : FlowState → Time → Domain → Pressure
    viscosity    : FlowState → Viscosity
    bodyForce    : FlowState → Force

    Incompressible : FlowState → Set
    MomentumEquation : FlowState → Set
    EnergyInequality : FlowState → Set
    WeakSolution     : FlowState → Set
    SmoothSolution   : FlowState → Set

record NavierStokesRegularityBoundary
  (F : FluidDynamicsLaw) : Set₁ where
  open FluidDynamicsLaw F
  field
    ThreeDimensional : Domain → Set
    FiniteEnergyData : FlowState → Set
    GlobalWeakSolution : FlowState → Set
    GlobalSmoothUnique : FlowState → Set

    weakExistenceLane :
      (state : FlowState) → FiniteEnergyData state →
      GlobalWeakSolution state

    regularityRemainsSeparate :
      (state : FlowState) → GlobalWeakSolution state → Set

record DiffusionTransportLaw : Set₁ where
  field
    State       : Set
    Concentration : Set
    Temperature : Set
    Gradient    : Set
    Flux        : Set
    Diffusivity : Set
    Conductivity : Set

    concentration : State → Concentration
    temperature   : State → Temperature
    concentrationGradient : State → Gradient
    temperatureGradient   : State → Gradient
    fickFlux      : Diffusivity → Gradient → Flux
    fourierHeatFlux : Conductivity → Gradient → Flux

record ReactionDiffusionLaw : Set₁ where
  field
    FieldState : Set
    ReactionRate : Set
    DiffusionOperator : Set
    TimeStep   : Set

    reaction   : FieldState → ReactionRate
    diffusion  : FieldState → DiffusionOperator
    evolve     : TimeStep → FieldState → FieldState
    PatternFormingInstability : FieldState → Set

record PlasmaMagnetofluidLaw : Set₁ where
  field
    PlasmaState    : Set
    ElectricField  : Set
    MagneticField  : Set
    Current        : Set
    ChargeDensity  : Set
    FluidVelocity  : Set

    electricField : PlasmaState → ElectricField
    magneticField : PlasmaState → MagneticField
    current       : PlasmaState → Current
    chargeDensity : PlasmaState → ChargeDensity
    fluidVelocity : PlasmaState → FluidVelocity

    MaxwellCompatible : PlasmaState → Set
    FluidBalanceCompatible : PlasmaState → Set
    OhmClosure : PlasmaState → Set

record WaveOpticsAcousticsLaw : Set₁ where
  field
    Field      : Set
    Medium     : Set
    Frequency  : Set
    WaveVector : Set
    Dispersion : Set
    Intensity  : Set

    dispersionRelation : Medium → Frequency → WaveVector → Dispersion
    propagate          : Medium → Field → Field
    intensity          : Field → Intensity
    Interference       : Field → Field → Set
    GeometricOpticsLimit : Field → Set
    AcousticLimit       : Field → Set

record ContinuumMaterialAuthorityBoundary : Set₁ where
  field
    balanceLawIsNotConstitutiveClosure : Set
    continuumCarrierRequiresScaleSeparation : Set
    viscosityAndElasticityRequireCalibration : Set
    weakSolutionIsNotSmoothRegularity : Set
    reactionDiffusionPatternIsNotBiologicalMeaning : Set
    idealMHDIsNotFullKineticPlasma : Set
    waveEquationRequiresBoundaryAndMediumData : Set
