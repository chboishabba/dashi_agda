module DASHI.Physics.Laws.ThermodynamicStatisticalLaws where

-- Thermodynamic laws constrain macrostates and processes.  Statistical
-- mechanics supplies a micro-to-macro representation only after a measure,
-- ensemble, limit, and ergodic/typicality assumptions are declared.
record ThermodynamicStateSpace : Set₁ where
  field
    State        : Set
    Energy       : Set
    Entropy      : Set
    Temperature  : Set
    Pressure     : Set
    Volume       : Set
    ParticleNumber : Set
    ChemicalPotential : Set

    internalEnergy : State → Energy
    entropy        : State → Entropy
    temperature    : State → Temperature
    pressure       : State → Pressure
    volume         : State → Volume
    particleNumber : State → ParticleNumber
    chemicalPotential : State → ChemicalPotential

record ZerothLaw
  (T : ThermodynamicStateSpace) : Set₁ where
  open ThermodynamicStateSpace T
  field
    ThermalEquilibrium : State → State → Set
    transitiveEquilibrium :
      (a b c : State) →
      ThermalEquilibrium a b →
      ThermalEquilibrium b c →
      ThermalEquilibrium a c
    equilibriumTemperatureCompatible :
      (a b : State) → ThermalEquilibrium a b → Set

record FirstLaw
  (T : ThermodynamicStateSpace) : Set₁ where
  open ThermodynamicStateSpace T
  field
    Process : Set
    Heat    : Set
    Work    : Set
    EnergyChange : Set

    heatTransferred : Process → Heat
    workDone        : Process → Work
    energyChange    : Process → EnergyChange
    energyBalance   : Process → Set

record SecondLaw
  (T : ThermodynamicStateSpace) : Set₁ where
  open ThermodynamicStateSpace T
  field
    Process : Set
    EntropyProduction : Set

    production : Process → EntropyProduction
    Nonnegative : EntropyProduction → Set
    admissibleProcess : Process → Set

    entropyProductionNonnegative :
      (process : Process) → admissibleProcess process →
      Nonnegative (production process)

record ThirdLaw
  (T : ThermodynamicStateSpace) : Set₁ where
  open ThermodynamicStateSpace T
  field
    LowTemperatureLimit : Set
    EntropyReference    : Set
    approachesReference : State → LowTemperatureLimit → EntropyReference → Set
    unattainabilityBoundary : LowTemperatureLimit → Set

record EquationOfState
  (T : ThermodynamicStateSpace) : Set₁ where
  open ThermodynamicStateSpace T
  field
    MaterialClass : Set
    Relation      : Set
    equation : MaterialClass → State → Relation
    ValidInRegime : MaterialClass → State → Set

record StatisticalEnsemble : Set₁ where
  field
    Microstate    : Set
    Macrostate    : Set
    Probability   : Set
    Energy        : Set
    Parameter     : Set
    PartitionValue : Set
    Observable    : Set
    Expectation   : Set

    macrostate    : Microstate → Macrostate
    probability   : Parameter → Microstate → Probability
    microEnergy   : Microstate → Energy
    partitionFunction : Parameter → PartitionValue
    expectation   : Parameter → Observable → Expectation

    Normalised    : Parameter → Set
    EnsembleAdmissible : Parameter → Set

record MicroMacroBridge
  (S : StatisticalEnsemble) : Set₁ where
  open StatisticalEnsemble S
  field
    ThermodynamicQuantity : Set
    macroObservable : Observable → ThermodynamicQuantity
    LimitParameter : Set
    Error          : Set

    finiteSizeError : LimitParameter → Observable → Error
    Controlled      : Error → Set
    thermodynamicLimitControlled :
      (limit : LimitParameter) (observable : Observable) →
      Controlled (finiteSizeError limit observable)

record FluctuationDissipationLaw : Set₁ where
  field
    EquilibriumState : Set
    Fluctuation      : Set
    Response         : Set
    Frequency        : Set
    Temperature      : Set

    fluctuationSpectrum : EquilibriumState → Frequency → Fluctuation
    linearResponse      : EquilibriumState → Frequency → Response
    relation            : Temperature → Fluctuation → Response → Set

record NonequilibriumTransportLaw : Set₁ where
  field
    State       : Set
    Force       : Set
    Flux        : Set
    Coefficient : Set
    EntropyProduction : Set

    thermodynamicForce : State → Force
    constitutiveFlux   : Coefficient → Force → Flux
    entropyProduction  : Force → Flux → EntropyProduction
    OnsagerCompatible  : Coefficient → Set
    PositiveProduction : EntropyProduction → Set

record StochasticDynamicsLaw : Set₁ where
  field
    State       : Set
    Time        : Set
    Transition  : Set
    Probability : Set
    StationaryDistribution : Set

    transitionProbability : Time → State → State → Probability
    stationary : StationaryDistribution → Set
    detailedBalance : StationaryDistribution → Transition → Set
    markovProperty : Transition → Set

record ThermodynamicStatisticalAuthorityBoundary : Set₁ where
  field
    entropyRequiresStateCoarseGraining : Set
    secondLawIsNotPointwiseMicroscopicMonotonicity : Set
    ensembleRequiresMeasureAndNormalisation : Set
    thermodynamicLimitRequiresUniformControl : Set
    ergodicityIsNotAutomatic : Set
    constitutiveCoefficientsRequireMaterialCalibration : Set
    fluctuationDissipationRequiresNearEquilibriumAssumptions : Set
