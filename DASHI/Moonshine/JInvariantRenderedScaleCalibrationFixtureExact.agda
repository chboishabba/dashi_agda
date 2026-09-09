module DASHI.Moonshine.JInvariantRenderedScaleCalibrationFixtureExact where

------------------------------------------------------------------------
-- CONCRETE RENDERED-SCALE CALIBRATION PROTOCOL FIXTURE
--
-- This is an executable exact fixture for the measurement protocol:
-- a rendered sample retains an exact measured scale; the analytic box is that
-- scale fibre; orbit containment means the exact orbit scale agrees.  Global
-- scale injectivity then compiles unique k.  This validates the protocol but
-- deliberately does NOT claim that a particular external raster screenshot
-- has already been metrologically calibrated by Agda.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.JInvariantOrderThreeOrbitBalancedTernaryBidiExact as Orbit
import DASHI.Moonshine.JInvariantOrderThreeSeamScaleRecognitionBidiExact as Scale
import DASHI.Moonshine.JInvariantRenderedIntervalOrbitRecognitionBidiExact as Rendered
import DASHI.Moonshine.JInvariantRenderedGlobalScaleCompilerBidiExact as Compiler

record RenderedScaleSample : Set where
  constructor rendered-scale-sample
  field
    sampleIndex : Nat
    measuredScale : Nat
    measuredScaleLaw : measuredScale ≡ Scale.seamScale sampleIndex

open RenderedScaleSample public

AnalyticPoint : Set
AnalyticPoint = Orbit.RhoOrbitCoordinate

AnalyticBox : Set
AnalyticBox = Nat

scaleCalibration :
  Rendered.RenderedAnalyticBoxCalibration
    RenderedScaleSample AnalyticPoint AnalyticBox
scaleCalibration = record
  { calibrateBox = measuredScale
  ; contains = λ box point →
      Scale.seamScale (Orbit.index point) ≡ box
  }

orbitRealisation : Rendered.AnalyticOrderThreeOrbitRealisation AnalyticPoint
orbitRealisation = record
  { realiseOrbitCoordinate = λ coordinate → coordinate
  }

sampleCertificate :
  (sample : RenderedScaleSample) →
  Compiler.RenderedGlobalScaleBoxCertificate
    scaleCalibration orbitRealisation sample
sampleCertificate sample = record
  { candidateIndex = sampleIndex sample
  ; measuredScale = measuredScale sample
  ; measuredScaleIsCandidateScale = measuredScaleLaw sample
  ; candidateContained = sym (measuredScaleLaw sample)
  ; everyContainedOrbitHasMeasuredScale = λ other contained → contained
  }

sampleRecognition :
  (sample : RenderedScaleSample) →
  Rendered.RenderedOrbitRecognition
    scaleCalibration orbitRealisation sample
sampleRecognition sample =
  Compiler.compileRenderedOrbitRecognition (sampleCertificate sample)

canonicalSampleAt : Nat → RenderedScaleSample
canonicalSampleAt k =
  rendered-scale-sample k (Scale.seamScale k) refl

canonicalSampleRecognisesItsIndex :
  (k : Nat) →
  Rendered.recognisedIndex (sampleRecognition (canonicalSampleAt k)) ≡ k
canonicalSampleRecognisesItsIndex k = refl

record RenderedCalibrationProtocolClosure : Set where
  constructor rendered-calibration-protocol-closure
  field
    concreteScaleSampleCarrierExact : Bool
    analyticScaleBoxExact : Bool
    orbitContainmentExact : Bool
    globalUniqueIndexCompilerInstantiated : Bool
    endToEndFixtureExact : Bool
    externalRasterMetrologyPerformedHere : Bool

canonicalRenderedCalibrationProtocolClosure : RenderedCalibrationProtocolClosure
canonicalRenderedCalibrationProtocolClosure =
  rendered-calibration-protocol-closure
    true true true true true false
