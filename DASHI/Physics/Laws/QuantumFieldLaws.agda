module DASHI.Physics.Laws.QuantumFieldLaws where

-- Quantum kinematics, dynamics, measurement, relativistic fields, and local
-- algebraic QFT are separate layers.  A finite phase carrier or unitary-like
-- update does not automatically provide a physical Hilbert/QFT model.
record QuantumKinematics : Set₁ where
  field
    Scalar       : Set
    State        : Set
    Observable   : Set
    Probability  : Set
    InnerProduct : State → State → Scalar

    Normalised   : State → Set
    SelfAdjoint  : Observable → Set
    expectation  : Observable → State → Scalar
    transitionProbability : State → State → Probability

record QuantumDynamics
  (Q : QuantumKinematics) : Set₁ where
  open QuantumKinematics Q
  field
    Time        : Set
    Hamiltonian : Set
    Evolution   : Time → State → State

    unitary : Time → Set
    schrodingerEquation : Hamiltonian → State → Set
    normPreserved :
      (time : Time) (state : State) → Normalised state →
      Normalised (Evolution time state)
    compositionLaw : Time → Time → State → Set

record QuantumMeasurement
  (Q : QuantumKinematics) : Set₁ where
  open QuantumKinematics Q
  field
    Outcome     : Set
    Measurement : Set
    PostState   : Set

    outcomeProbability : Measurement → State → Outcome → Probability
    updateAfterOutcome  : Measurement → State → Outcome → PostState
    ProbabilitiesNormalised : Measurement → State → Set
    BornCompatible : Measurement → State → Set

    measurementIsNotUnitaryEvolutionByDefinition : Set

record RelativisticQuantumField : Set₁ where
  field
    SpacetimeRegion : Set
    Field           : Set
    Spinor          : Set
    DiracOperator   : Set
    LocalObservable : SpacetimeRegion → Set
    State           : Set
    Vacuum          : Set
    Correlation     : Set

    fieldAt         : SpacetimeRegion → Field
    diracEquation   : DiracOperator → Spinor → Set
    correlation     : State → SpacetimeRegion → SpacetimeRegion → Correlation

    CausallySeparated : SpacetimeRegion → SpacetimeRegion → Set
    Microcausal       : SpacetimeRegion → SpacetimeRegion → Set
    SpectrumCondition : State → Set
    VacuumInvariant   : Vacuum → Set
    LocalCovariance   : SpacetimeRegion → Set

record AlgebraicQFTLaw : Set₁ where
  field
    Region          : Set
    LocalAlgebra    : Region → Set
    Inclusion       : Region → Region → Set
    CausalSeparation : Region → Region → Set
    Morphism        : Region → Region → Set

    isotony      : {small large : Region} → Inclusion small large → Morphism small large
    locality     : (left right : Region) → CausalSeparation left right → Set
    timeSlice    : Region → Region → Set
    covariance   : Region → Set

record QuantumStatisticalLaw
  (Q : QuantumKinematics) : Set₁ where
  open QuantumKinematics Q
  field
    DensityState : Set
    Channel      : Set
    Entropy      : Set

    evolveDensity : Channel → DensityState → DensityState
    tracePreserving : Channel → Set
    completelyPositive : Channel → Set
    entropy : DensityState → Entropy
    equilibriumState : DensityState → Set

record QuantumClassicalLimit : Set₁ where
  field
    QuantumState    : Set
    ClassicalState  : Set
    ScaleParameter  : Set
    QuantumObservable : Set
    ClassicalObservable : Set
    Error           : Set

    stateLimit      : ScaleParameter → QuantumState → ClassicalState
    observableLimit : QuantumObservable → ClassicalObservable
    correspondenceError : ScaleParameter → QuantumState → Error
    Controlled      : Error → Set

    correspondenceControlled :
      (scale : ScaleParameter) (state : QuantumState) →
      Controlled (correspondenceError scale state)

record QuantumFieldAuthorityBoundary : Set₁ where
  field
    finiteCarrierIsNotPhysicalHilbertSpace : Set
    selfAdjointnessRequiresDomainControl : Set
    bornRuleRequiresMeasurementAdapter : Set
    diracStructureIsNotInteractingQFT : Set
    aqftSocketsAreNotConcreteLocalAlgebras : Set
    renormalisedPredictionsRequireSchemeAndCalibration : Set
    quantumClassicalLimitRequiresUniformErrorControl : Set
