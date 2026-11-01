module DASHI.Physics.GR.GravitationalWavePolarizationSignBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.GR.GravitationalWavePolarizationSourceAttributionExact as Source
import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as SignedG

------------------------------------------------------------------------
-- GW POLARIZATION BASIS != WAVEFORM SIGN != DETECTOR-RESPONSE SIGN != G SIGN
--
-- The externally sourced GR statement is only that the tensor-polarization
-- basis contains plus and cross modes.  The sign decomposition below is a
-- DASHI reconstruction/internal theorem surface.
------------------------------------------------------------------------

data TensorPolarizationBasis : Set where
  plusTensorPolarization : TensorPolarizationBasis
  crossTensorPolarization : TensorPolarizationBasis

data WaveformAmplitudeSign : Set where
  positiveWaveformAmplitude : WaveformAmplitudeSign
  zeroWaveformAmplitude : WaveformAmplitudeSign
  negativeWaveformAmplitude : WaveformAmplitudeSign

data DetectorResponseSign : Set where
  positiveDetectorResponse : DetectorResponseSign
  zeroDetectorResponse : DetectorResponseSign
  negativeDetectorResponse : DetectorResponseSign

data ReadoutSign : Set where
  positiveReadout : ReadoutSign
  zeroReadout : ReadoutSign
  negativeReadout : ReadoutSign

record TensorPolarizationComponent : Set where
  constructor tensor-polarization-component
  field
    basis : TensorPolarizationBasis
    amplitudeSign : WaveformAmplitudeSign

open TensorPolarizationComponent public

------------------------------------------------------------------------
-- Exact collisions.
------------------------------------------------------------------------

data PlusSignFixture : Set where
  plusPositiveFixture : PlusSignFixture
  plusNegativeFixture : PlusSignFixture

plusFixtureBasis : PlusSignFixture → TensorPolarizationBasis
plusFixtureBasis _ = plusTensorPolarization

plusFixtureAmplitudeSign : PlusSignFixture → WaveformAmplitudeSign
plusFixtureAmplitudeSign plusPositiveFixture = positiveWaveformAmplitude
plusFixtureAmplitudeSign plusNegativeFixture = negativeWaveformAmplitude

samePlusBasisCollision :
  plusFixtureBasis plusPositiveFixture ≡ plusFixtureBasis plusNegativeFixture
samePlusBasisCollision = refl

plusBasisDoesNotDetermineWaveformSign :
  plusFixtureAmplitudeSign plusPositiveFixture
    ≡ plusFixtureAmplitudeSign plusNegativeFixture → ⊥
plusBasisDoesNotDetermineWaveformSign ()

data SameSignDifferentBasisFixture : Set where
  plusPositiveBasisFixture : SameSignDifferentBasisFixture
  crossPositiveBasisFixture : SameSignDifferentBasisFixture

fixtureWaveformSign : SameSignDifferentBasisFixture → WaveformAmplitudeSign
fixtureWaveformSign _ = positiveWaveformAmplitude

fixturePolarizationBasis : SameSignDifferentBasisFixture → TensorPolarizationBasis
fixturePolarizationBasis plusPositiveBasisFixture = plusTensorPolarization
fixturePolarizationBasis crossPositiveBasisFixture = crossTensorPolarization

sameWaveformSignCollision :
  fixtureWaveformSign plusPositiveBasisFixture
    ≡ fixtureWaveformSign crossPositiveBasisFixture
sameWaveformSignCollision = refl

waveformSignDoesNotDeterminePolarizationBasis :
  fixturePolarizationBasis plusPositiveBasisFixture
    ≡ fixturePolarizationBasis crossPositiveBasisFixture → ⊥
waveformSignDoesNotDeterminePolarizationBasis ()

------------------------------------------------------------------------
-- Detector-response sign product.
--
-- At sign-only level a waveform sign reversal can be traded against a detector
-- response sign reversal.  This is why detector response/calibration must be
-- fixed in the +/-G paired comparator.
------------------------------------------------------------------------

readoutSign : WaveformAmplitudeSign → DetectorResponseSign → ReadoutSign
readoutSign zeroWaveformAmplitude detector = zeroReadout
readoutSign waveform zeroDetectorResponse = zeroReadout
readoutSign positiveWaveformAmplitude positiveDetectorResponse = positiveReadout
readoutSign positiveWaveformAmplitude negativeDetectorResponse = negativeReadout
readoutSign negativeWaveformAmplitude positiveDetectorResponse = negativeReadout
readoutSign negativeWaveformAmplitude negativeDetectorResponse = positiveReadout

data DetectorSignFixture : Set where
  negativeWavePositiveResponse : DetectorSignFixture
  positiveWaveNegativeResponse : DetectorSignFixture

fixtureAmplitude : DetectorSignFixture → WaveformAmplitudeSign
fixtureAmplitude negativeWavePositiveResponse = negativeWaveformAmplitude
fixtureAmplitude positiveWaveNegativeResponse = positiveWaveformAmplitude

fixtureDetectorResponse : DetectorSignFixture → DetectorResponseSign
fixtureDetectorResponse negativeWavePositiveResponse = positiveDetectorResponse
fixtureDetectorResponse positiveWaveNegativeResponse = negativeDetectorResponse

coarseReadoutSign : DetectorSignFixture → ReadoutSign
coarseReadoutSign fixture =
  readoutSign (fixtureAmplitude fixture) (fixtureDetectorResponse fixture)

readoutSignCollision :
  coarseReadoutSign negativeWavePositiveResponse
    ≡ coarseReadoutSign positiveWaveNegativeResponse
readoutSignCollision = refl

record RefinedDetectorSignObserver : Set where
  constructor refined-detector-sign-observer
  field
    waveformSign : WaveformAmplitudeSign
    detectorSign : DetectorResponseSign

refinedDetectorObserve : DetectorSignFixture → RefinedDetectorSignObserver
refinedDetectorObserve fixture =
  refined-detector-sign-observer
    (fixtureAmplitude fixture)
    (fixtureDetectorResponse fixture)

refinedDetectorFixturesDistinct :
  refinedDetectorObserve negativeWavePositiveResponse
    ≡ refinedDetectorObserve positiveWaveNegativeResponse → ⊥
refinedDetectorFixturesDistinct ()

------------------------------------------------------------------------
-- Attribution and coupling-sign boundaries.
------------------------------------------------------------------------

externalGRPolarizationBasisReceipt :
  Source.PolarizationSourceEntitlement Source.grHasTwoTensorPolarizations
externalGRPolarizationBasisReceipt =
  Source.canonicalPolarizationSourceEntitlement Source.grHasTwoTensorPolarizations

record GravitationalWavePolarizationSignBoundary : Set where
  constructor gravitational-wave-polarization-sign-boundary
  field
    plusMeansPositivePolarity : Bool
    crossMeansNegativePolarity : Bool
    eachTensorBasisMayCarryEitherNonzeroWaveformSign : Bool
    waveformSignDeterminesPolarizationBasis : Bool
    detectorReadoutSignDeterminesWaveformSignWithoutResponseReceipt : Bool
    polarizationBasisDeterminesCouplingSign : Bool
    waveformSignDeterminesCouplingSign : Bool
    detectorReadoutSignDeterminesCouplingSign : Bool
    plusCrossStatementIsExternallyAttributed : Bool
    signSeparationIsDASHIReconstruction : Bool

canonicalGravitationalWavePolarizationSignBoundary :
  GravitationalWavePolarizationSignBoundary
canonicalGravitationalWavePolarizationSignBoundary =
  gravitational-wave-polarization-sign-boundary
    false false true false false false false false true true

------------------------------------------------------------------------
-- Explicit sign-coordinate non-collapse with Newton coupling sign.
------------------------------------------------------------------------

data PolarizationCouplingFixture : Set where
  plusPositiveGFixture : PolarizationCouplingFixture
  plusNegativeGFixture : PolarizationCouplingFixture

polarizationBasisObserver : PolarizationCouplingFixture → TensorPolarizationBasis
polarizationBasisObserver _ = plusTensorPolarization

couplingSignConsumer : PolarizationCouplingFixture → SignedG.CouplingSign
couplingSignConsumer plusPositiveGFixture = SignedG.positiveCoupling
couplingSignConsumer plusNegativeGFixture = SignedG.negativeCoupling

polarizationBasisCollisionAcrossGSign :
  polarizationBasisObserver plusPositiveGFixture
    ≡ polarizationBasisObserver plusNegativeGFixture
polarizationBasisCollisionAcrossGSign = refl

polarizationBasisCannotRecoverGSign :
  couplingSignConsumer plusPositiveGFixture
    ≡ couplingSignConsumer plusNegativeGFixture → ⊥
polarizationBasisCannotRecoverGSign ()
