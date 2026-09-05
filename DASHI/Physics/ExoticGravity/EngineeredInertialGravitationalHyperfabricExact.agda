module DASHI.Physics.ExoticGravity.EngineeredInertialGravitationalHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ENGINEERED INERTIAL-GRAVITATIONAL RESPONSE HYPERFABRIC
--
-- The object is deliberately broader than "antigravity".  A reported force,
-- impulse, weight change, inertial anomaly, or metric effect occupies a
-- different fibre coordinate and may have a different ordinary explanation.
------------------------------------------------------------------------

record MatterGravityBase : Set₁ where
  constructor matter-gravity-base
  field
    MaterialPhase CollectiveState Geometry Environment : Set
    sourceScope : String

open MatterGravityBase public

record MatterGravityFibre (base : MatterGravityBase) : Set₁ where
  constructor matter-gravity-fibre
  field
    HiggsSector ElectromagneticField ElectricCurrent : Set
    MassCurrent AngularMomentum StressEnergy : Set
    InertialMass PassiveGravitationalResponse : Set
    ActiveGravitationalSource MetricResponse MomentumOutput : Set
    ExperimentalResidual : Set

open MatterGravityFibre public

record GravityHypervoxel : Set₁ where
  constructor gravity-hypervoxel
  field
    base : MatterGravityBase
    fibre : MatterGravityFibre base

open GravityHypervoxel public

GravityHyperfabric : Set₁
GravityHyperfabric = GravityHypervoxel

------------------------------------------------------------------------
-- Distinct negative-mass coordinates.
--
-- A Higgs-generated fermion mass parameter, inertial mass, passive response,
-- and active gravitational source are not definitionally the same coordinate.
------------------------------------------------------------------------

record NegativeMassCoordinateBoundary : Set where
  constructor negative-mass-coordinate-boundary
  field
    higgsMassIsInertialMass : Bool
    higgsMassIsInertialMassIsFalse : higgsMassIsInertialMass ≡ false

    higgsMassIsPassiveGravitationalMass : Bool
    higgsMassIsPassiveGravitationalMassIsFalse :
      higgsMassIsPassiveGravitationalMass ≡ false

    higgsSignFlipImpliesNegativeMacroscopicMass : Bool
    higgsSignFlipImpliesNegativeMacroscopicMassIsFalse :
      higgsSignFlipImpliesNegativeMacroscopicMass ≡ false

    activeGravityIsStressEnergyCoordinate : Bool
    activeGravityIsStressEnergyCoordinateIsTrue :
      activeGravityIsStressEnergyCoordinate ≡ true

canonicalNegativeMassCoordinateBoundary : NegativeMassCoordinateBoundary
canonicalNegativeMassCoordinateBoundary =
  negative-mass-coordinate-boundary
    false refl
    false refl
    false refl
    true refl

------------------------------------------------------------------------
-- Standard-physics baseline.
--
-- Superconducting coherence can change internal energy, current, stress, and
-- field configuration.  Standard GR does not add a separate multiplicative
-- gravitational charge merely because a state is coherent.
------------------------------------------------------------------------

record StandardPhysicsBaseline : Set where
  constructor standard-physics-baseline
  field
    gravitySourcesStressEnergy : Bool
    gravitySourcesStressEnergyIsTrue : gravitySourcesStressEnergy ≡ true

    phaseTransitionMayChangeStressEnergy : Bool
    phaseTransitionMayChangeStressEnergyIsTrue :
      phaseTransitionMayChangeStressEnergy ≡ true

    coherenceAloneIsIndependentGravitationalCharge : Bool
    coherenceAloneIsIndependentGravitationalChargeIsFalse :
      coherenceAloneIsIndependentGravitationalCharge ≡ false

    ordinaryMomentumChannelsMustBeClosedFirst : Bool
    ordinaryMomentumChannelsMustBeClosedFirstIsTrue :
      ordinaryMomentumChannelsMustBeClosedFirst ≡ true

canonicalStandardPhysicsBaseline : StandardPhysicsBaseline
canonicalStandardPhysicsBaseline =
  standard-physics-baseline true refl true refl false refl true refl

------------------------------------------------------------------------
-- Candidate new-physics departure chart.
--
-- These are alternatives, not assumed facts.  A candidate can depart in one
-- narrow channel without asserting that every other coordinate is anomalous.
------------------------------------------------------------------------

data DepartureChannel : Set where
  noDeparture : DepartureChannel
  coherentCurrentGravityCoupling : DepartureChannel
  effectiveGravityCouplingChange : DepartureChannel
  inertialMassVariation : DepartureChannel
  passiveGravityVariation : DepartureChannel
  activeStressEnergyAnomaly : DepartureChannel
  metricEngineering : DepartureChannel
  unexplainedMomentumResidual : DepartureChannel

record CandidateDeparture : Set₁ where
  constructor candidate-departure
  field
    channel : DepartureChannel
    OrderParameter NewMediator ConstitutiveResponse : Set
    proposedMechanism : String

open CandidateDeparture public

------------------------------------------------------------------------
-- The Higgs analogy is structural, not an identification.
------------------------------------------------------------------------

record OrderParameterAnalogyBoundary : Set where
  constructor order-parameter-analogy-boundary
  field
    higgsAndSuperconductingCondensateAreSameField : Bool
    higgsAndSuperconductingCondensateAreSameFieldIsFalse :
      higgsAndSuperconductingCondensateAreSameField ≡ false

    bothCanBeRepresentedAsOrderedPhaseCoordinates : Bool
    bothCanBeRepresentedAsOrderedPhaseCoordinatesIsTrue :
      bothCanBeRepresentedAsOrderedPhaseCoordinates ≡ true

    orderedPhaseImpliesNewGravityCoupling : Bool
    orderedPhaseImpliesNewGravityCouplingIsFalse :
      orderedPhaseImpliesNewGravityCoupling ≡ false

canonicalOrderParameterAnalogyBoundary : OrderParameterAnalogyBoundary
canonicalOrderParameterAnalogyBoundary =
  order-parameter-analogy-boundary false refl true refl false refl

------------------------------------------------------------------------
-- Output non-factorability.
------------------------------------------------------------------------

record ObservableProjectionBoundary : Set where
  constructor observable-projection-boundary
  field
    thrustImpliesGravityModification : Bool
    thrustImpliesGravityModificationIsFalse :
      thrustImpliesGravityModification ≡ false

    weightChangeImpliesMetricChange : Bool
    weightChangeImpliesMetricChangeIsFalse :
      weightChangeImpliesMetricChange ≡ false

    momentumResidualImpliesNegativeMass : Bool
    momentumResidualImpliesNegativeMassIsFalse :
      momentumResidualImpliesNegativeMass ≡ false

    mechanismReceiptRequiredForMechanismClaim : Bool
    mechanismReceiptRequiredForMechanismClaimIsTrue :
      mechanismReceiptRequiredForMechanismClaim ≡ true

canonicalObservableProjectionBoundary : ObservableProjectionBoundary
canonicalObservableProjectionBoundary =
  observable-projection-boundary false refl false refl false refl true refl
