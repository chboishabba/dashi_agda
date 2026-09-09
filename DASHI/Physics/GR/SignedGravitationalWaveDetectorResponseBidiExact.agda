module DASHI.Physics.GR.SignedGravitationalWaveDetectorResponseBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE-STRAIN SIGN x DETECTOR-RESPONSE SIGN
--
-- A detector readout is not a naked source-strain sign.  At a deliberately
-- coarse sign-only level, flipping source strain and flipping detector-response
-- orientation can produce the same effective readout sign.  Calibration and
-- detector-response identity therefore remain load-bearing coordinates.
------------------------------------------------------------------------

data StrainSign : Set where
  positiveStrain : StrainSign
  zeroStrain : StrainSign
  negativeStrain : StrainSign

data DetectorResponseSign : Set where
  positiveDetectorResponse : DetectorResponseSign
  zeroDetectorResponse : DetectorResponseSign
  negativeDetectorResponse : DetectorResponseSign

data EffectiveReadoutSign : Set where
  positiveReadout : EffectiveReadoutSign
  zeroReadout : EffectiveReadoutSign
  negativeReadout : EffectiveReadoutSign

effectiveReadoutSign : StrainSign → DetectorResponseSign → EffectiveReadoutSign
effectiveReadoutSign zeroStrain response = zeroReadout
effectiveReadoutSign strain zeroDetectorResponse = zeroReadout
effectiveReadoutSign positiveStrain positiveDetectorResponse = positiveReadout
effectiveReadoutSign positiveStrain negativeDetectorResponse = negativeReadout
effectiveReadoutSign negativeStrain positiveDetectorResponse = negativeReadout
effectiveReadoutSign negativeStrain negativeDetectorResponse = positiveReadout

------------------------------------------------------------------------
-- Exact coarse collision.
------------------------------------------------------------------------

data ReadoutFixture : Set where
  negativeStrainPositiveDetector : ReadoutFixture
  positiveStrainNegativeDetector : ReadoutFixture

fixtureStrain : ReadoutFixture → StrainSign
fixtureStrain negativeStrainPositiveDetector = negativeStrain
fixtureStrain positiveStrainNegativeDetector = positiveStrain

fixtureDetectorResponse : ReadoutFixture → DetectorResponseSign
fixtureDetectorResponse negativeStrainPositiveDetector = positiveDetectorResponse
fixtureDetectorResponse positiveStrainNegativeDetector = negativeDetectorResponse

coarseReadoutObserver : ReadoutFixture → EffectiveReadoutSign
coarseReadoutObserver fixture =
  effectiveReadoutSign (fixtureStrain fixture) (fixtureDetectorResponse fixture)

readoutSignCollision :
  coarseReadoutObserver negativeStrainPositiveDetector
    ≡ coarseReadoutObserver positiveStrainNegativeDetector
readoutSignCollision = refl

record RefinedReadoutObserver : Set where
  constructor refined-readout-observer
  field
    strainSign : StrainSign
    detectorResponseSign : DetectorResponseSign

refinedReadoutObserve : ReadoutFixture → RefinedReadoutObserver
refinedReadoutObserve fixture =
  refined-readout-observer (fixtureStrain fixture) (fixtureDetectorResponse fixture)

refinedReadoutFixturesDistinct :
  refinedReadoutObserve negativeStrainPositiveDetector
    ≡ refinedReadoutObserve positiveStrainNegativeDetector → ⊥
refinedReadoutFixturesDistinct ()

------------------------------------------------------------------------
-- Calibration-bound observation package.  No canonical experimental receipt
-- is manufactured here.
------------------------------------------------------------------------

record CalibratedWaveReadout : Set where
  constructor calibrated-wave-readout
  field
    detectorResponseCarrier : String
    detectorCalibrationCarrier : String
    detectorCalibrationRevision : String
    sourceStrainSign : StrainSign
    responseSign : DetectorResponseSign
    observedReadoutSign : EffectiveReadoutSign
    readoutMatches :
      observedReadoutSign ≡ effectiveReadoutSign sourceStrainSign responseSign

open CalibratedWaveReadout public

record SignedWaveDetectorBoundary : Set where
  constructor signed-wave-detector-boundary
  field
    rawReadoutSignAloneDeterminesSourceStrainSign : Bool
    detectorResponseSignMustBeRetained : Bool
    detectorCalibrationMustBeRetained : Bool
    sameDetectorResponseRequiredForSignedGPair : Bool
    oppositeSourceStrainAutomaticallyMeansOppositeRecordedReadout : Bool
    calibratedNetworkMayRefineSourceSignInference : Bool
    readoutSignAloneDeterminesMatterCouplingSign : Bool

canonicalSignedWaveDetectorBoundary : SignedWaveDetectorBoundary
canonicalSignedWaveDetectorBoundary =
  signed-wave-detector-boundary false true true true false true false
