module DASHI.Physics.Laws.GaugeInteractionLaws where

-- Gauge geometry supplies connection, curvature, covariance, and identities.
-- Physical interaction claims additionally require an action, matter coupling,
-- source currents, equations of motion, units, and empirical observables.
record GaugeFieldGeometry : Set₁ where
  field
    BasePoint      : Set
    GaugeGroup     : Set
    GaugeTransformation : Set
    Connection     : Set
    Curvature      : Set
    MatterField    : Set

    gaugeActConnection : GaugeTransformation → Connection → Connection
    gaugeActMatter     : GaugeTransformation → MatterField → MatterField
    curvature          : Connection → Curvature
    covariantDerivative : Connection → MatterField → MatterField

    bianchiIdentity : Connection → Set
    curvatureCovariant : GaugeTransformation → Connection → Set

record MaxwellFieldLaw : Set₁ where
  field
    Spacetime      : Set
    OneForm        : Set
    TwoForm        : Set
    ThreeForm      : Set
    Metric         : Set
    Orientation    : Set
    ChargeCurrent  : Set
    Force          : Set
    Velocity       : Set

    potential      : OneForm
    fieldStrength  : OneForm → TwoForm
    exteriorD      : TwoForm → ThreeForm
    hodgeStar      : Metric → Orientation → TwoForm → TwoForm
    currentForm    : ChargeCurrent → ThreeForm
    lorentzForce   : TwoForm → ChargeCurrent → Velocity → Force

    homogeneousEquation : exteriorD (fieldStrength potential) → Set
    inhomogeneousEquation : Metric → Orientation → ChargeCurrent → Set
    currentConservation : ChargeCurrent → Set

record YangMillsFieldLaw : Set₁ where
  field
    GaugeGeometry  : GaugeFieldGeometry
    Action         : Set
    SourceCurrent  : Set
    Equation       : Set
    Energy         : Set

    actionOf : GaugeFieldGeometry.Connection GaugeGeometry → Action
    source   : GaugeFieldGeometry.MatterField GaugeGeometry → SourceCurrent
    fieldEquation :
      GaugeFieldGeometry.Connection GaugeGeometry → SourceCurrent → Equation
    energy : GaugeFieldGeometry.Curvature GaugeGeometry → Energy

    gaugeInvariantAction : Set
    covariantCurrentConservation : SourceCurrent → Set
    stationarityGivesFieldEquation :
      GaugeFieldGeometry.Connection GaugeGeometry → Set

record InteractionSectorSystem : Set₁ where
  field
    State       : Set
    StrongSector : State → Set
    WeakSector   : State → Set
    ElectromagneticSector : State → Set
    GravitationalSector   : State → Set

    StrongObservable : Set
    WeakObservable   : Set
    EMObservable     : Set
    GravityObservable : Set

    observeStrong : State → StrongObservable
    observeWeak   : State → WeakObservable
    observeEM     : State → EMObservable
    observeGravity : State → GravityObservable

record GaugeMatterCoupling : Set₁ where
  field
    GaugeField  : Set
    MatterField : Set
    Current     : Set
    Coupling    : Set
    Action      : Set

    coupledAction : Coupling → GaugeField → MatterField → Action
    currentFromMatter : MatterField → Current
    GaugeInvariant : Action → Set
    CurrentConserved : Current → Set

record GaugeConstraintQuantisationBoundary : Set₁ where
  field
    ClassicalConfiguration : Set
    GaugeOrbit             : Set
    PhysicalState          : Set
    Constraint             : Set
    GaugeFixing            : Set

    orbitOf       : ClassicalConfiguration → GaugeOrbit
    imposeConstraint : Constraint → ClassicalConfiguration → Set
    quotientState : GaugeOrbit → PhysicalState
    gaugeFix      : GaugeFixing → ClassicalConfiguration → ClassicalConfiguration

    GribovControlled : GaugeFixing → Set
    quotientIndependentOfRepresentative : GaugeOrbit → Set

record GaugeInteractionAuthorityBoundary : Set₁ where
  field
    curvatureIsNotFieldEquation : Set
    bianchiIsNotSourceEquation : Set
    homogeneousMaxwellIsNotFullMaxwell : Set
    sourceCurrentRequiresMatterExtraction : Set
    gaugeFixingRequiresGribovControl : Set
    latticeYangMillsIsNotContinuumMassGap : Set
    finiteGaugeNamesAreNotStandardModelUniqueness : Set
