module DASHI.Physics.Laws.PhysicalLawCore where

open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

-- Laws are indexed by domain, regime, mathematical role, and authority status.
-- This prevents a finite carrier identity, continuum theorem, effective
-- constitutive law, and measured calibration from being reported as the same
-- kind of result.
data PhysicalDomain : Set where
  spacetimeGeometry      : PhysicalDomain
  classicalMechanics     : PhysicalDomain
  quantumMechanics       : PhysicalDomain
  quantumFieldTheory     : PhysicalDomain
  electromagnetism       : PhysicalDomain
  gaugeInteractions      : PhysicalDomain
  standardModel          : PhysicalDomain
  gravitation            : PhysicalDomain
  cosmology              : PhysicalDomain
  thermodynamics         : PhysicalDomain
  statisticalMechanics   : PhysicalDomain
  continuumMechanics     : PhysicalDomain
  fluidDynamics          : PhysicalDomain
  materialPhysics        : PhysicalDomain
  plasmaPhysics          : PhysicalDomain
  opticsAcoustics        : PhysicalDomain
  atomicMolecularPhysics : PhysicalDomain
  nuclearParticlePhysics : PhysicalDomain
  metrology              : PhysicalDomain
  effectiveTheory        : PhysicalDomain

data PhysicalRegime : Set where
  discreteRegime       : PhysicalRegime
  continuumRegime      : PhysicalRegime
  classicalRegime      : PhysicalRegime
  quantumRegime        : PhysicalRegime
  relativisticRegime   : PhysicalRegime
  nonrelativisticRegime : PhysicalRegime
  microscopicRegime    : PhysicalRegime
  mesoscopicRegime     : PhysicalRegime
  macroscopicRegime    : PhysicalRegime
  equilibriumRegime    : PhysicalRegime
  nonequilibriumRegime : PhysicalRegime
  weakFieldRegime      : PhysicalRegime
  strongFieldRegime    : PhysicalRegime
  perturbativeRegime   : PhysicalRegime
  nonperturbativeRegime : PhysicalRegime

data PhysicalLawKind : Set where
  kinematicLaw      : PhysicalLawKind
  dynamicalLaw      : PhysicalLawKind
  constraintLaw     : PhysicalLawKind
  conservationLaw   : PhysicalLawKind
  symmetryLaw       : PhysicalLawKind
  constitutiveLaw   : PhysicalLawKind
  stochasticLaw     : PhysicalLawKind
  statisticalLaw    : PhysicalLawKind
  effectiveLaw      : PhysicalLawKind
  calibrationLaw    : PhysicalLawKind
  limitLaw          : PhysicalLawKind

data LawClaimStatus : Set where
  exactStructuralTheorem : LawClaimStatus
  concreteFiniteInstance : LawClaimStatus
  conditionalAnalyticBridge : LawClaimStatus
  effectiveModelWithAssumptions : LawClaimStatus
  empiricalCalibrationRequired : LawClaimStatus
  externalAuthorityRequired : LawClaimStatus
  openMathematicalProblem : LawClaimStatus
  notPromoted : LawClaimStatus

record PhysicalLawSurface : Set₁ where
  field
    State       : Set
    Context     : Set
    Parameter   : Set
    Observable  : Set
    Symmetry    : Set
    Conserved   : Set

    domain      : PhysicalDomain
    regimes     : List PhysicalRegime
    kind        : PhysicalLawKind
    status      : LawClaimStatus
    lawName     : String

    evolves     : Context → Parameter → State → State → Set
    admissible  : Context → Parameter → State → Set
    observe     : Context → State → Observable
    symmetryAct : Symmetry → State → State
    conservedAt : Conserved → State → Set

record PhysicalLawWitness
  (L : PhysicalLawSurface) : Set₁ where
  open PhysicalLawSurface L
  field
    context   : Context
    parameter : Parameter
    initial final : State

    initialAdmissible : admissible context parameter initial
    finalAdmissible   : admissible context parameter final
    evolution         : evolves context parameter initial final

record SymmetryConservationBridge
  (L : PhysicalLawSurface) : Set₁ where
  open PhysicalLawSurface L
  field
    ContinuousSymmetry : Symmetry → Set
    ChargeFor          : Symmetry → Conserved

    noetherCompatible :
      (symmetry : Symmetry) → ContinuousSymmetry symmetry →
      (state : State) → conservedAt (ChargeFor symmetry) state

record DimensionalConsistency : Set₁ where
  field
    Quantity  : Set
    Dimension : Set
    Equation  : Set

    dimensionOf : Quantity → Dimension
    WellDimensioned : Equation → Set

record CausalLocalityBoundary
  (L : PhysicalLawSurface) : Set₁ where
  open PhysicalLawSurface L
  field
    Region : Set
    CausallySeparated : Region → Region → Set
    LocalObservableAt : Region → Observable → Set
    LocalityCompatible : Region → Region → Set

record WellPosednessBoundary
  (L : PhysicalLawSurface) : Set₁ where
  open PhysicalLawSurface L
  field
    InitialData : Set
    Solution    : Set
    HasSolution : InitialData → Solution → Set
    UniqueInClass : InitialData → Solution → Set
    StableUnderPerturbation : InitialData → Set

record EmpiricalAuthorityBoundary
  (L : PhysicalLawSurface) : Set₁ where
  field
    Dataset      : Set
    Measurement  : Set
    Calibration  : Set
    Validation   : Set

    calibrates   : Calibration → PhysicalLawSurface.Parameter L → Set
    predicts     : PhysicalLawSurface.Context L →
                   PhysicalLawSurface.State L → Measurement
    validatedBy  : Validation → Dataset → Set

-- Equality of labels or equations is not enough to identify physical laws:
-- domain, regime, carrier, units, assumptions, and calibration must agree.
record LawIdentityBoundary
  (left right : PhysicalLawSurface) : Set₁ where
  field
    SameCarrier : Set
    SameRegime  : Set
    SameUnits   : Set
    SameAssumptions : Set
    SameObservables : Set

    carrierWitness : SameCarrier
    regimeWitness  : SameRegime
    unitsWitness   : SameUnits
    assumptionsWitness : SameAssumptions
    observablesWitness : SameObservables
