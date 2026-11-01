module DASHI.Physics.ExoticGravity.SuperconductingTransitionOrderParameterLockBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.SuperconductingSourceConstitutiveEvidenceBidiExact as Evidence
import DASHI.Physics.ExoticGravity.SuperconductingGravityCouplingResidualBidiExact as Coupling
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- TRANSITION LOCK != TEMPERATURE THRESHOLD
--
-- A candidate superconducting-gravity response must track the measured
-- superconducting/order-parameter state on the same apparatus.  Merely being
-- above/below a nominal Tc is a control coordinate, not a transition receipt.
------------------------------------------------------------------------

data TemperatureBand : Set where
  aboveNominalTc : TemperatureBand
  belowNominalTc : TemperatureBand

data SuperconductingState : Set where
  normalState : SuperconductingState
  coherentSuperconductingState : SuperconductingState
  transitionStateUnresolved : SuperconductingState

data OrderParameterStatus : Set where
  orderParameterAbsent : OrderParameterStatus
  orderParameterPresent : OrderParameterStatus
  orderParameterUnresolved : OrderParameterStatus

------------------------------------------------------------------------
-- Introspective collision: equal temperature classification does not determine
-- the consumer-relevant phase/order-parameter state.
------------------------------------------------------------------------

data TransitionFixture : Set where
  belowTcCoherentFixture : TransitionFixture
  belowTcUnresolvedFixture : TransitionFixture

temperatureObserver : TransitionFixture → TemperatureBand
temperatureObserver _ = belowNominalTc

stateConsumer : TransitionFixture → SuperconductingState
stateConsumer belowTcCoherentFixture = coherentSuperconductingState
stateConsumer belowTcUnresolvedFixture = transitionStateUnresolved

temperatureCollision :
  temperatureObserver belowTcCoherentFixture
    ≡ temperatureObserver belowTcUnresolvedFixture
temperatureCollision = refl

temperatureBandDoesNotDetermineSuperconductingState :
  stateConsumer belowTcCoherentFixture
    ≡ stateConsumer belowTcUnresolvedFixture → ⊥
temperatureBandDoesNotDetermineSuperconductingState ()

------------------------------------------------------------------------
-- Typed transition-lock receipt.
------------------------------------------------------------------------

record TransitionOrderParameterLockReceipt : Set₁ where
  constructor transition-order-parameter-lock-receipt
  field
    apparatusIdentity : String
    runIdentity : String
    temperatureBand : TemperatureBand
    superconductingState : SuperconductingState
    orderParameterStatus : OrderParameterStatus

    ThermometryReceipt : Set
    thermometryReceipt : ThermometryReceipt

    OrderParameterMeasurementReceipt : Set
    orderParameterMeasurementReceipt : OrderParameterMeasurementReceipt

    TransitionIdentityReceipt : Set
    transitionIdentityReceipt : TransitionIdentityReceipt

    SameApparatusSourceNormalisationReceipt : Set
    sameApparatusSourceNormalisationReceipt : SameApparatusSourceNormalisationReceipt

    SameGeometryReceipt : Set
    sameGeometryReceipt : SameGeometryReceipt

    BackgroundClosureReceipt : Set
    backgroundClosureReceipt : BackgroundClosureReceipt

    stateIsCoherent : superconductingState ≡ coherentSuperconductingState
    orderParameterIsPresent : orderParameterStatus ≡ orderParameterPresent

open TransitionOrderParameterLockReceipt public

------------------------------------------------------------------------
-- Thin proof-search specialization: this pays the existing transition-lock
-- concept; it does not replace the evidence state machine.
------------------------------------------------------------------------

data TransitionLockResidual : Set where
  missingThermometry : TransitionLockResidual
  missingOrderParameterMeasurement : TransitionLockResidual
  missingTransitionIdentity : TransitionLockResidual
  missingSourceNormalisation : TransitionLockResidual
  missingGeometryIdentity : TransitionLockResidual
  missingBackgroundClosure : TransitionLockResidual
  transitionMismatchOpen : TransitionLockResidual

producerForTransitionLockResidual :
  TransitionLockResidual → Search.ProducerClass
producerForTransitionLockResidual missingThermometry = Search.empiricalEvidenceProducer
producerForTransitionLockResidual missingOrderParameterMeasurement = Search.empiricalEvidenceProducer
producerForTransitionLockResidual missingTransitionIdentity = Search.identityProducer
producerForTransitionLockResidual missingSourceNormalisation = Search.identityProducer
producerForTransitionLockResidual missingGeometryIdentity = Search.identityProducer
producerForTransitionLockResidual missingBackgroundClosure = Search.empiricalEvidenceProducer
producerForTransitionLockResidual transitionMismatchOpen = Search.contradictionProducer

existingTransitionRequirement : Coupling.DiscriminatorRequirement
existingTransitionRequirement = Coupling.phaseRequirement

postSourceEvidenceState : Evidence.EvidenceClosureState
postSourceEvidenceState = Evidence.evidence-closure-state true false true false true false

postSourceFirstOpenIsTransitionLock :
  Evidence.firstOpenEvidenceLeaf postSourceEvidenceState
    ≡ Evidence.transitionLockLeaf
postSourceFirstOpenIsTransitionLock = refl

record TransitionOrderParameterBoundary : Set where
  constructor transition-order-parameter-boundary
  field
    belowNominalTcAutomaticallyMeansCoherentState : Bool
    temperatureCrossingAlonePaysTransitionLock : Bool
    orderParameterMeasurementRequired : Bool
    sameApparatusSourceNormalisationRequired : Bool
    matchedGeometryRequired : Bool
    matchedBackgroundClosureRequired : Bool
    transitionLockAutomaticallyProvesConstitutiveNegativeG : Bool

canonicalTransitionOrderParameterBoundary : TransitionOrderParameterBoundary
canonicalTransitionOrderParameterBoundary =
  transition-order-parameter-boundary false false true true true true false
