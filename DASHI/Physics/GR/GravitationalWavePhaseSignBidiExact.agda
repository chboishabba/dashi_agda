module DASHI.Physics.GR.GravitationalWavePhaseSignBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.GR.GravitationalWavePolarizationSourceAttributionExact as Source
import DASHI.Physics.GR.GravitationalWavePolarizationSignBidiExact as Polarization
import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as SignedG

------------------------------------------------------------------------
-- PHASE != POLARIZATION BASIS != SIGN(G)
--
-- The external LIGO technical carrier is source-entitled only for phase and
-- polarization angle being separate detector/model coordinates.  The finite
-- phase/sign involution below is a DASHI reconstruction used to expose an
-- observer collision; it is not attributed to that carrier as a theorem.
------------------------------------------------------------------------

data PhaseParity : Set where
  referencePhase : PhaseParity
  halfCycleShift : PhaseParity

phaseFlip : Polarization.WaveformAmplitudeSign → Polarization.WaveformAmplitudeSign
phaseFlip Polarization.positiveWaveformAmplitude = Polarization.negativeWaveformAmplitude
phaseFlip Polarization.zeroWaveformAmplitude = Polarization.zeroWaveformAmplitude
phaseFlip Polarization.negativeWaveformAmplitude = Polarization.positiveWaveformAmplitude

phaseFlipInvolutive :
  (sign : Polarization.WaveformAmplitudeSign) →
  phaseFlip (phaseFlip sign) ≡ sign
phaseFlipInvolutive Polarization.positiveWaveformAmplitude = refl
phaseFlipInvolutive Polarization.zeroWaveformAmplitude = refl
phaseFlipInvolutive Polarization.negativeWaveformAmplitude = refl

applyPhaseParity :
  PhaseParity → Polarization.WaveformAmplitudeSign → Polarization.WaveformAmplitudeSign
applyPhaseParity referencePhase sign = sign
applyPhaseParity halfCycleShift sign = phaseFlip sign

------------------------------------------------------------------------
-- Exact collision: same polarization basis, opposite signed component solely
-- because the phase coordinate differs.
------------------------------------------------------------------------

data PhaseFixture : Set where
  plusReferenceFixture : PhaseFixture
  plusHalfCycleFixture : PhaseFixture

fixtureBasis : PhaseFixture → Polarization.TensorPolarizationBasis
fixtureBasis _ = Polarization.plusTensorPolarization

fixturePhase : PhaseFixture → PhaseParity
fixturePhase plusReferenceFixture = referencePhase
fixturePhase plusHalfCycleFixture = halfCycleShift

fixtureBaseSign : PhaseFixture → Polarization.WaveformAmplitudeSign
fixtureBaseSign _ = Polarization.positiveWaveformAmplitude

fixtureObservedSign : PhaseFixture → Polarization.WaveformAmplitudeSign
fixtureObservedSign fixture = applyPhaseParity (fixturePhase fixture) (fixtureBaseSign fixture)

sameBasisAcrossPhaseCollision :
  fixtureBasis plusReferenceFixture ≡ fixtureBasis plusHalfCycleFixture
sameBasisAcrossPhaseCollision = refl

phaseChangesSignedComponentWithoutChangingBasis :
  fixtureObservedSign plusReferenceFixture
    ≡ fixtureObservedSign plusHalfCycleFixture → ⊥
phaseChangesSignedComponentWithoutChangingBasis ()

record RefinedPhaseSignObserver : Set where
  constructor refined-phase-sign-observer
  field
    basis : Polarization.TensorPolarizationBasis
    phase : PhaseParity
    amplitudeSign : Polarization.WaveformAmplitudeSign

refinedObserve : PhaseFixture → RefinedPhaseSignObserver
refinedObserve fixture =
  refined-phase-sign-observer
    (fixtureBasis fixture)
    (fixturePhase fixture)
    (fixtureObservedSign fixture)

refinedFixturesDistinct :
  refinedObserve plusReferenceFixture ≡ refinedObserve plusHalfCycleFixture → ⊥
refinedFixturesDistinct ()

------------------------------------------------------------------------
-- External source entitlement remains bounded.
------------------------------------------------------------------------

phaseCoordinateSourceReceipt :
  Source.DetectorResponseSourceEntitlement
    Source.detectorResponseDependsOnPolarizationAngleAndPhase
phaseCoordinateSourceReceipt =
  Source.canonicalDetectorResponseSourceEntitlement
    Source.detectorResponseDependsOnPolarizationAngleAndPhase

------------------------------------------------------------------------
-- Coupling-sign collision: phase/waveform sign alone does not recover G sign.
------------------------------------------------------------------------

data PhaseCouplingFixture : Set where
  positiveGNegativeWaveFixture : PhaseCouplingFixture
  negativeGNegativeWaveFixture : PhaseCouplingFixture

coarseWaveSign : PhaseCouplingFixture → Polarization.WaveformAmplitudeSign
coarseWaveSign _ = Polarization.negativeWaveformAmplitude

couplingSign : PhaseCouplingFixture → SignedG.CouplingSign
couplingSign positiveGNegativeWaveFixture = SignedG.positiveCoupling
couplingSign negativeGNegativeWaveFixture = SignedG.negativeCoupling

waveSignCollisionAcrossCoupling :
  coarseWaveSign positiveGNegativeWaveFixture
    ≡ coarseWaveSign negativeGNegativeWaveFixture
waveSignCollisionAcrossCoupling = refl

waveformSignCannotRecoverGSign :
  couplingSign positiveGNegativeWaveFixture
    ≡ couplingSign negativeGNegativeWaveFixture → ⊥
waveformSignCannotRecoverGSign ()

record GravitationalWavePhaseSignBoundary : Set where
  constructor gravitational-wave-phase-sign-boundary
  field
    phaseIsSeparateCoordinate : Bool
    halfCycleMayReverseSignedComponentInThisFiniteModel : Bool
    phaseChangeChangesPolarizationBasisAutomatically : Bool
    negativeWaveformSampleMeansNegativeG : Bool
    phaseCoordinateSourceReceiptProvesDASHIPhaseInvolution : Bool
    refinedObserverRetainsBasisPhaseAndSign : Bool

canonicalGravitationalWavePhaseSignBoundary : GravitationalWavePhaseSignBoundary
canonicalGravitationalWavePhaseSignBoundary =
  gravitational-wave-phase-sign-boundary true true false false false true
