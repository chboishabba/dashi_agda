module DASHI.Physics.Laws.GravityCosmologyLaws where

open import DASHI.Physics.Laws.SpacetimeMechanicsLaws

-- General relativity requires differential geometry, a stress-energy source,
-- an Einstein equation, constraint propagation, and a selected solution class.
record EinsteinGravityLaw : Set₁ where
  field
    Geometry      : DifferentialGeometricDynamics
    Metric        : Set
    EinsteinTensor : Set
    StressEnergy   : Set
    Coupling       : Set
    CosmologicalConstant : Set
    Equation       : Set

    einsteinTensor : Metric → EinsteinTensor
    stressEnergy   : Metric → StressEnergy
    fieldEquation  : Coupling → CosmologicalConstant →
                     EinsteinTensor → StressEnergy → Equation

    ContractedBianchi : EinsteinTensor → Set
    StressEnergyConserved : StressEnergy → Set
    ConstraintSatisfied : Metric → Set
    FieldEquationSatisfied : EinsteinTensor → StressEnergy → Set

    bianchiImpliesSourceConservation :
      (tensor : EinsteinTensor) (source : StressEnergy) →
      ContractedBianchi tensor →
      FieldEquationSatisfied tensor source →
      StressEnergyConserved source

record GravityInitialValueProblem
  (G : EinsteinGravityLaw) : Set₁ where
  field
    InitialSlice : Set
    InitialData  : Set
    SpacetimeSolution : Set

    HamiltonianConstraint : InitialData → Set
    MomentumConstraint    : InitialData → Set
    EvolvesTo             : InitialData → SpacetimeSolution → Set
    GloballyHyperbolic     : SpacetimeSolution → Set
    MaximalDevelopment    : InitialData → SpacetimeSolution → Set

record WeakFieldNewtonianLimit
  (G : EinsteinGravityLaw) : Set₁ where
  field
    RelativisticMetric : Set
    NewtonianPotential : Set
    SourceDensity      : Set
    SmallParameter     : Set
    Error              : Set

    potentialFromMetric : SmallParameter → RelativisticMetric → NewtonianPotential
    poissonEquation     : NewtonianPotential → SourceDensity → Set
    approximationError  : SmallParameter → RelativisticMetric → Error
    Controlled          : Error → Set

record SphericalVacuumLaw
  (G : EinsteinGravityLaw) : Set₁ where
  field
    SphericalMetric : Set
    MassParameter   : Set
    Vacuum          : SphericalMetric → Set
    Static          : SphericalMetric → Set
    SphericallySymmetric : SphericalMetric → Set
    SchwarzschildClass : MassParameter → SphericalMetric → Set

record CosmologicalDynamics : Set₁ where
  field
    CosmicTime     : Set
    ScaleFactor    : Set
    EnergyDensity  : Set
    Pressure       : Set
    Curvature      : Set
    CosmologicalConstant : Set
    Equation       : Set

    scaleFactor    : CosmicTime → ScaleFactor
    density        : CosmicTime → EnergyDensity
    pressure       : CosmicTime → Pressure
    friedmannEquation : Curvature → CosmologicalConstant → Equation
    accelerationEquation : CosmologicalConstant → Equation
    continuityEquation : Equation

record GravitationalWaveLaw
  (G : EinsteinGravityLaw) : Set₁ where
  field
    BackgroundMetric : Set
    Perturbation      : Set
    GaugeCondition    : Set
    WaveEquation      : Set
    ObservableStrain  : Set

    linearise       : BackgroundMetric → Perturbation → WaveEquation
    imposeGauge     : GaugeCondition → Perturbation → Set
    strainObservable : Perturbation → ObservableStrain
    weakFieldValid  : BackgroundMetric → Perturbation → Set

record GravityCosmologyAuthorityBoundary : Set₁ where
  field
    lorentzSignatureIsNotEinsteinDynamics : Set
    bianchiIdentityNeedsFieldEquationForMatterConservation : Set
    discreteCurvatureIsNotContinuumGR : Set
    weakFieldLimitRequiresQuantitativeErrorBound : Set
    schwarzschildCandidateRequiresVacuumUniqueness : Set
    friedmannEquationsRequireHomogeneityIsotropyAndMatterModel : Set
    cosmologicalParametersRequireObservation : Set
    quantumGravityNotDerived : Set
