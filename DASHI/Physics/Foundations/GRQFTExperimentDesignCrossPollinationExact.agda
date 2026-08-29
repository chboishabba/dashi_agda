module DASHI.Physics.Foundations.GRQFTExperimentDesignCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ExperimentalCoordinateDesignExact as Design
import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Physics.Foundations.PhysicalTheoryExperimentDiscriminationExact as Physical
import DASHI.Programmes.QuantumFalsifiableTargetExact as Quantum

------------------------------------------------------------------------
-- GR/QFT EXPERIMENT-DESIGN CROSS-POLLINATION
--
-- The existing physical promotion gate already says a candidate must recover
-- established GR and low-energy QFT regimes, expose a novel observable, and
-- connect it to a falsifiable measurement.  This module sharpens the experiment
-- design question: which coordinates are reference invariants/regime checks,
-- which may be controlled, which are observables, and which newly derived
-- discriminators enlarge the current theory-separating language.
--
-- Repository-native architecture only.  No quantum-gravity theory or empirical
-- prediction is promoted here.
------------------------------------------------------------------------

data FundamentalExperimentCoordinate : Set where
  grRecoveryCoordinate
  qftRecoveryCoordinate
  emergentLocalityCoordinate
  lorentzViolationCoordinate
  emergentRandomnessCoordinate
  projectionTimeAsymmetryCoordinate
  apparatusControlCoordinate
  nuisanceSystematicCoordinate
  derivedTheoryDiscriminatorCoordinate
  : FundamentalExperimentCoordinate

coordinateRole : FundamentalExperimentCoordinate → Design.CoordinateRole
coordinateRole grRecoveryCoordinate = Design.referenceInvariant
coordinateRole qftRecoveryCoordinate = Design.referenceInvariant
coordinateRole emergentLocalityCoordinate = Design.measuredObservable
coordinateRole lorentzViolationCoordinate = Design.measuredObservable
coordinateRole emergentRandomnessCoordinate = Design.measuredObservable
coordinateRole projectionTimeAsymmetryCoordinate = Design.measuredObservable
coordinateRole apparatusControlCoordinate = Design.controlledInput
coordinateRole nuisanceSystematicCoordinate = Design.nuisanceCoordinate
coordinateRole derivedTheoryDiscriminatorCoordinate = Design.derivedDiscriminator

------------------------------------------------------------------------
-- The five programme targets are already owned by QuantumFalsifiableTargetExact.
-- We expose their intended experiment-design roles without asserting that any
-- target has yet been measured or that its physical coordinate is unique.
------------------------------------------------------------------------

targetCoordinate : Quantum.QuantumResearchTarget → FundamentalExperimentCoordinate
targetCoordinate Quantum.emergentLocality = emergentLocalityCoordinate
targetCoordinate Quantum.lorentzInvarianceViolation = lorentzViolationCoordinate
targetCoordinate Quantum.emergentRandomness = emergentRandomnessCoordinate
targetCoordinate Quantum.projectionTimeAsymmetry = projectionTimeAsymmetryCoordinate
targetCoordinate Quantum.lowEnergyRecovery = qftRecoveryCoordinate

------------------------------------------------------------------------
-- Promotion obligations become an experiment-design cutset.  Recovery regimes
-- are constraints/reference tests; a new observable plus measurement supplies a
-- possible discriminator.  A knob/control changes apparatus conditions, not the
-- fundamental law being tested.
------------------------------------------------------------------------

record GRQFTExperimentDesignCutset : Set₁ where
  constructor grqftExperimentDesignCutset
  field
    physicalCandidate : Physical.FundamentalPhysicalCandidate
    grRegimeReferenceCoordinate : FundamentalExperimentCoordinate
    qftRegimeReferenceCoordinate : FundamentalExperimentCoordinate
    novelObservableCoordinate : FundamentalExperimentCoordinate
    falsifiableMeasurementCoordinate : FundamentalExperimentCoordinate

    grCoordinateIsReferenceInvariant :
      coordinateRole grRegimeReferenceCoordinate ≡ Design.referenceInvariant
    qftCoordinateIsReferenceInvariant :
      coordinateRole qftRegimeReferenceCoordinate ≡ Design.referenceInvariant
    novelCoordinateIsObservedOrDerived :
      (coordinateRole novelObservableCoordinate ≡ Design.measuredObservable)
      ⊎
      (coordinateRole novelObservableCoordinate ≡ Design.derivedDiscriminator)

    recoveryValidationReference : String
    observableDerivationReference : String
    measurementProtocolReference : String
    nuisanceControlReference : String

open GRQFTExperimentDesignCutset public

------------------------------------------------------------------------
-- Informational dimensionality.
--
-- Adding a new observable/derived discriminator can enlarge the experiment
-- language by splitting theories that were equivalent under the old language.
-- This is the useful sense in which experiment design can add a "dimension":
-- a new independent coordinate of discrimination.  It is explicitly not the
-- creation of a new spacetime or SI physical dimension.
------------------------------------------------------------------------

record InformationalDimensionGain
    (Theory Experiment Observation : Set)
    (predicts : Physical.Predictions Theory Experiment Observation)
    (oldLanguage : Physical.Language Experiment)
    (left right : Theory) : Set₁ where
  constructor informationalDimensionGain
  field
    newExperiment : Experiment
    oldCandidatesEquivalent : Physical.EquivalentOn oldLanguage predicts left right
    newExperimentDiscriminates :
      Physical.Discriminates predicts newExperiment left right
    newCoordinateReference : String
    physicalDimensionInterpretationReference : String

open InformationalDimensionGain public

------------------------------------------------------------------------
-- Measurement and fidelity escalation share the generic actionability objective.
-- In fundamental physics the obstruction can literally be current theory
-- equivalence: choose a declared measurement, apparatus perturbation, replication
-- or higher-fidelity instrument/model that splits the candidate class cheaply
-- enough while still satisfying independent experimental authority/safety.
------------------------------------------------------------------------

record GRQFTActionabilityExperimentSearch : Set₁ where
  constructor grqftActionabilityExperimentSearch
  field
    problem : Choice.ActionabilityProblem
    DeclaredMove : Choice.InformationMove → Set
    cheapestResolution :
      Choice.CheapestAuthorisingInformationMove problem DeclaredMove
    candidateTheoryReference : String
    currentEquivalenceReference : String
    apparatusCapabilityReference : String
    systematicErrorReference : String

open GRQFTActionabilityExperimentSearch public

record GRQFTExperimentDesignBoundary : Set where
  constructor grqftExperimentDesignBoundary
  field
    grAndQFTRecoveryAreFreeExperimentalControls : Bool
    grAndQFTRecoveryAreFreeExperimentalControlsIsFalse :
      grAndQFTRecoveryAreFreeExperimentalControls ≡ false

    apparatusControlMeansChangingFundamentalLaw : Bool
    apparatusControlMeansChangingFundamentalLawIsFalse :
      apparatusControlMeansChangingFundamentalLaw ≡ false

    addingDiscriminatorCreatesNewPhysicalDimension : Bool
    addingDiscriminatorCreatesNewPhysicalDimensionIsFalse :
      addingDiscriminatorCreatesNewPhysicalDimension ≡ false

    addingDiscriminatorCanIncreaseInformationalDimension : Bool
    addingDiscriminatorCanIncreaseInformationalDimensionIsTrue :
      addingDiscriminatorCanIncreaseInformationalDimension ≡ true

    currentQuantumTargetsAreEstablishedQuantumGravityObservables : Bool
    currentQuantumTargetsAreEstablishedQuantumGravityObservablesIsFalse :
      currentQuantumTargetsAreEstablishedQuantumGravityObservables ≡ false

canonicalGRQFTExperimentDesignBoundary : GRQFTExperimentDesignBoundary
canonicalGRQFTExperimentDesignBoundary =
  grqftExperimentDesignBoundary
    false refl false refl false refl true refl false refl
