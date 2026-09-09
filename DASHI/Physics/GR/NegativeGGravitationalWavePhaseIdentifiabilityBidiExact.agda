module DASHI.Physics.GR.NegativeGGravitationalWavePhaseIdentifiabilityBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Interop.SourceAttributionShapePolicyExact as Shape
import DASHI.Physics.GR.GravitationalWavePolarizationSourceAttributionExact as Source
import DASHI.Physics.GR.GravitationalWavePolarizationSignBidiExact as Polarization
import DASHI.Physics.GR.GravitationalWavePhaseSignBidiExact as Phase
import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as SignedG

------------------------------------------------------------------------
-- PHASE ANCHOR REQUIRED FOR WAVEFORM-SIGN IDENTIFIABILITY
--
-- External source entitlement: phase/polarization are separate detector/model
-- coordinates.  Internal DASHI finite model: a half-cycle phase reversal and a
-- frozen coupling-sign reversal can collide at the same coarse waveform sign.
-- This does not claim that a self-consistent negative-G binary equals a phase-
-- shifted positive-G binary.
------------------------------------------------------------------------

data SignExplanation : Set where
  phaseShiftExplanation : SignExplanation
  couplingSignExplanation : SignExplanation

data PhaseAnchorStatus : Set where
  phaseUnanchored phaseIndependentlyAnchored : PhaseAnchorStatus

data IdentifiabilityFixture : Set where
  positiveGHalfCycleFixture negativeGFrozenSignFixture : IdentifiabilityFixture

fixtureWaveformSign : IdentifiabilityFixture → Polarization.WaveformAmplitudeSign
fixtureWaveformSign _ = Polarization.negativeWaveformAmplitude

fixtureCouplingSign : IdentifiabilityFixture → SignedG.CouplingSign
fixtureCouplingSign positiveGHalfCycleFixture = SignedG.positiveCoupling
fixtureCouplingSign negativeGFrozenSignFixture = SignedG.negativeCoupling

fixturePhase : IdentifiabilityFixture → Phase.PhaseParity
fixturePhase positiveGHalfCycleFixture = Phase.halfCycleShift
fixturePhase negativeGFrozenSignFixture = Phase.referencePhase

fixtureExplanation : IdentifiabilityFixture → SignExplanation
fixtureExplanation positiveGHalfCycleFixture = phaseShiftExplanation
fixtureExplanation negativeGFrozenSignFixture = couplingSignExplanation

coarseWaveformSignCollision :
  fixtureWaveformSign positiveGHalfCycleFixture
    ≡ fixtureWaveformSign negativeGFrozenSignFixture
coarseWaveformSignCollision = refl

waveformSignDoesNotDetermineExplanation :
  fixtureExplanation positiveGHalfCycleFixture
    ≡ fixtureExplanation negativeGFrozenSignFixture → ⊥
waveformSignDoesNotDetermineExplanation ()

record RefinedWaveSignObserver : Set where
  constructor refined-wave-sign-observer
  field
    waveformSign : Polarization.WaveformAmplitudeSign
    phase : Phase.PhaseParity
    couplingSign : SignedG.CouplingSign
    explanation : SignExplanation

refinedObserve : IdentifiabilityFixture → RefinedWaveSignObserver
refinedObserve fixture =
  refined-wave-sign-observer
    (fixtureWaveformSign fixture)
    (fixturePhase fixture)
    (fixtureCouplingSign fixture)
    (fixtureExplanation fixture)

refinedFixturesDistinct :
  refinedObserve positiveGHalfCycleFixture
    ≡ refinedObserve negativeGFrozenSignFixture → ⊥
refinedFixturesDistinct ()

------------------------------------------------------------------------
-- Source entitlement remains bounded to the phase coordinate itself.
------------------------------------------------------------------------

phaseCoordinateSourceReceipt :
  Source.DetectorResponseSourceEntitlement
    Source.detectorResponseDependsOnPolarizationAngleAndPhase
phaseCoordinateSourceReceipt =
  Source.canonicalDetectorResponseSourceEntitlement
    Source.detectorResponseDependsOnPolarizationAngleAndPhase

internalAttributionShape : Shape.RequiredAttributionShape
internalAttributionShape = Shape.requiredAttributionShape Shape.internalDerivedTheorem

------------------------------------------------------------------------
-- A real signed-G waveform discriminator must carry phase anchoring separately.
------------------------------------------------------------------------

record NegativeGWaveSignDiscriminator : Set₁ where
  constructor negative-g-wave-sign-discriminator
  field
    phaseAnchorStatus : PhaseAnchorStatus
    phaseIsAnchored : phaseAnchorStatus ≡ phaseIndependentlyAnchored

    DetectorResponseCalibration : Set
    detectorResponseCalibration : DetectorResponseCalibration

    PositiveGSourceSolution : Set
    positiveGSourceSolution : PositiveGSourceSolution

    NegativeGSourceSolution : Set
    negativeGSourceSolution : NegativeGSourceSolution

    SameSourceLawReceipt : Set
    sameSourceLawReceipt : SameSourceLawReceipt

    SamePropagationConventionReceipt : Set
    samePropagationConventionReceipt : SamePropagationConventionReceipt

open NegativeGWaveSignDiscriminator public

record NegativeGWavePhaseIdentifiabilityBoundary : Set where
  constructor negative-g-wave-phase-identifiability-boundary
  field
    negativeWaveformSignAloneIdentifiesNegativeG : Bool
    independentPhaseAnchorRequired : Bool
    detectorResponseCalibrationRequired : Bool
    signConditionedSourceSolutionsRequired : Bool
    sameSourceLawAndPropagationConventionRequired : Bool
    ligoPhaseSourceProvesDASHICollisionTheorem : Bool
    frozenSignCollisionEqualsSelfConsistentNegativeGWaveform : Bool

canonicalNegativeGWavePhaseIdentifiabilityBoundary :
  NegativeGWavePhaseIdentifiabilityBoundary
canonicalNegativeGWavePhaseIdentifiabilityBoundary =
  negative-g-wave-phase-identifiability-boundary
    false true true true true false false
