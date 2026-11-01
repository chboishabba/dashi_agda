module DASHI.Physics.Laws.SpacetimeMechanicsLaws where

open import DASHI.Physics.Laws.PhysicalLawCore

-- Relativistic kinematics is separated from dynamics: causal classification and
-- Lorentz symmetry do not by themselves supply an equation of motion.
record SpacetimeKinematics : Set₁ where
  field
    Event       : Set
    Displacement : Set
    Interval    : Set
    Frame       : Set
    LorentzTransformation : Set

    displacement : Event → Event → Displacement
    interval     : Displacement → Interval
    transform    : LorentzTransformation → Frame → Event → Event

    Timelike  : Displacement → Set
    Null      : Displacement → Set
    Spacelike : Displacement → Set
    FutureDirected : Displacement → Set

    intervalInvariant :
      LorentzTransformation → Frame → Event → Event → Set

record DifferentialGeometricDynamics : Set₁ where
  field
    Manifold   : Set
    Point      : Manifold → Set
    Tangent    : (M : Manifold) → Point M → Set
    Metric     : Manifold → Set
    Connection : Manifold → Set
    Curvature  : Manifold → Set
    Geodesic   : Manifold → Set

    leviCivitaCompatible :
      (M : Manifold) → Metric M → Connection M → Set
    torsionFree :
      (M : Manifold) → Connection M → Set
    curvatureFromConnection :
      (M : Manifold) → Connection M → Curvature M
    bianchiIdentity :
      (M : Manifold) → Curvature M → Set
    geodesicEquation :
      (M : Manifold) → Metric M → Connection M → Geodesic M → Set

record VariationalMechanics : Set₁ where
  field
    Configuration : Set
    Time          : Set
    Path          : Set
    Variation     : Set
    Lagrangian    : Set
    ActionValue   : Set

    pathAt      : Path → Time → Configuration
    action      : Lagrangian → Path → ActionValue
    variedPath  : Variation → Path → Path
    Stationary  : Lagrangian → Path → Set
    EulerLagrange : Lagrangian → Path → Set

    stationarityImpliesEulerLagrange :
      (L : Lagrangian) (path : Path) →
      Stationary L path → EulerLagrange L path

record HamiltonianMechanics : Set₁ where
  field
    PhaseState     : Set
    Observable     : Set
    Hamiltonian    : Set
    Time           : Set
    SymplecticForm : Set
    PoissonBracket : Observable → Observable → Observable

    flow          : Hamiltonian → Time → PhaseState → PhaseState
    energy        : Hamiltonian → PhaseState → Observable
    HamiltonEquation : Hamiltonian → PhaseState → Set
    Symplectic     : SymplecticForm → Set
    FlowPreservesSymplectic : Hamiltonian → SymplecticForm → Set
    EnergyConserved : Hamiltonian → PhaseState → Set

record NoetherLaw : Set₁ where
  field
    VariationalSystem : VariationalMechanics
    Symmetry          : Set
    ConservedQuantity : Set

    ActsOnPath :
      Symmetry → VariationalMechanics.Path VariationalSystem →
      VariationalMechanics.Path VariationalSystem
    LeavesActionInvariant : Symmetry → Set
    charge : Symmetry → ConservedQuantity
    ConservedAlongSolutions : ConservedQuantity → Set

    noetherBridge :
      (symmetry : Symmetry) → LeavesActionInvariant symmetry →
      ConservedAlongSolutions (charge symmetry)

record ClassicalForceLaw : Set₁ where
  field
    Body      : Set
    Position  : Set
    Velocity  : Set
    Momentum  : Set
    Force     : Set
    Mass      : Set
    Time      : Set

    position : Body → Time → Position
    velocity : Body → Time → Velocity
    momentum : Body → Time → Momentum
    netForce : Body → Time → Force

    momentumLaw : Body → Time → Set
    forceEqualsMomentumRate : Body → Time → Set
    actionReactionBoundary : Body → Body → Time → Set

-- The Newtonian, geometrical-optics, and classical-field limits require a
-- controlled approximation map, not merely deletion of quantum or relativistic
-- vocabulary.
record MechanicsLimitBridge : Set₁ where
  field
    FineState   : Set
    CoarseState : Set
    Scale       : Set
    Error       : Set

    coarseGrain : Scale → FineState → CoarseState
    approximationError : Scale → FineState → Error
    Controlled : Error → Set

    limitControlled :
      (scale : Scale) (state : FineState) →
      Controlled (approximationError scale state)

record SpacetimeMechanicsAuthorityBoundary : Set₁ where
  field
    lorentzKinematicsIsNotGravity : Set
    actionPrincipleRequiresBoundaryConditions : Set
    noetherRequiresContinuousSymmetryAndRegularity : Set
    hamiltonianFormRequiresLegendreControl : Set
    classicalLimitRequiresErrorBound : Set
    geodesicMotionDoesNotCoverAllForces : Set
