module DASHI.Moonshine.JInvariantRenderedGlobalScaleCompilerBidiExact where

------------------------------------------------------------------------
-- RENDERED BOX -> EXACT SCALE -> GLOBAL UNIQUE k
--
-- Global injectivity of D_k = k^2+k+1 means a concrete calibration no longer
-- has to supply a separate all-Nat orbit-uniqueness theorem.  It retains its
-- analytic box and certifies only:
--
--   * one candidate k is contained,
--   * the measured exact scale is D_k,
--   * every orbit point contained in the same box has that same exact scale.
--
-- Scale injectivity then compiles the full RenderedOrbitRecognition record.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.JInvariantOrderThreeOrbitBalancedTernaryBidiExact as Orbit
import DASHI.Moonshine.JInvariantOrderThreeSeamScaleRecognitionBidiExact as Scale
import DASHI.Moonshine.JInvariantOrderThreeScaleGlobalInjectiveExact as Global
import DASHI.Moonshine.JInvariantRenderedIntervalOrbitRecognitionBidiExact as Rendered
import DASHI.Core.FrontierRelationStrengthBidiExact as Relation

record RenderedGlobalScaleBoxCertificate
    {RenderedPoint AnalyticPoint AnalyticBox : Set}
    (calibration : Rendered.RenderedAnalyticBoxCalibration
      RenderedPoint AnalyticPoint AnalyticBox)
    (realisation : Rendered.AnalyticOrderThreeOrbitRealisation AnalyticPoint)
    (sample : RenderedPoint) : Set where
  constructor rendered-global-scale-box-certificate
  field
    candidateIndex : Nat
    measuredScale : Nat
    measuredScaleIsCandidateScale :
      measuredScale ≡ Scale.seamScale candidateIndex
    candidateContained :
      Rendered.contains calibration
        (Rendered.calibrateBox calibration sample)
        (Rendered.realiseOrbitCoordinate realisation
          (Orbit.rhoOrbitCoordinate candidateIndex))
    everyContainedOrbitHasMeasuredScale :
      (other : Nat) →
      Rendered.contains calibration
        (Rendered.calibrateBox calibration sample)
        (Rendered.realiseOrbitCoordinate realisation
          (Orbit.rhoOrbitCoordinate other)) →
      Scale.seamScale other ≡ measuredScale

open RenderedGlobalScaleBoxCertificate public

containedOrbitHasCandidateIndex :
  {RenderedPoint AnalyticPoint AnalyticBox : Set} →
  {calibration : Rendered.RenderedAnalyticBoxCalibration
    RenderedPoint AnalyticPoint AnalyticBox} →
  {realisation : Rendered.AnalyticOrderThreeOrbitRealisation AnalyticPoint} →
  {sample : RenderedPoint} →
  (certificate : RenderedGlobalScaleBoxCertificate
    calibration realisation sample) →
  (other : Nat) →
  Rendered.contains calibration
    (Rendered.calibrateBox calibration sample)
    (Rendered.realiseOrbitCoordinate realisation
      (Orbit.rhoOrbitCoordinate other)) →
  other ≡ candidateIndex certificate
containedOrbitHasCandidateIndex certificate other contained =
  Global.seamScaleInjective
    other
    (candidateIndex certificate)
    (trans
      (everyContainedOrbitHasMeasuredScale certificate other contained)
      (measuredScaleIsCandidateScale certificate))

compileRenderedOrbitRecognition :
  {RenderedPoint AnalyticPoint AnalyticBox : Set} →
  {calibration : Rendered.RenderedAnalyticBoxCalibration
    RenderedPoint AnalyticPoint AnalyticBox} →
  {realisation : Rendered.AnalyticOrderThreeOrbitRealisation AnalyticPoint} →
  {sample : RenderedPoint} →
  RenderedGlobalScaleBoxCertificate calibration realisation sample →
  Rendered.RenderedOrbitRecognition calibration realisation sample
compileRenderedOrbitRecognition certificate =
  Rendered.rendered-orbit-recognition
    (candidateIndex certificate)
    (candidateContained certificate)
    (containedOrbitHasCandidateIndex certificate)

compiledRecognitionToScalePoint :
  {RenderedPoint AnalyticPoint AnalyticBox : Set} →
  {calibration : Rendered.RenderedAnalyticBoxCalibration
    RenderedPoint AnalyticPoint AnalyticBox} →
  {realisation : Rendered.AnalyticOrderThreeOrbitRealisation AnalyticPoint} →
  {sample : RenderedPoint} →
  (certificate : RenderedGlobalScaleBoxCertificate
    calibration realisation sample) →
  Scale.SeamScaleIndexedPoint
compiledRecognitionToScalePoint certificate =
  Rendered.recognitionToScalePoint
    (compileRenderedOrbitRecognition certificate)

renderedGlobalScaleRelation : Relation.RelationKind
renderedGlobalScaleRelation = Relation.exactCertificateSchemaReuse

record RenderedGlobalScaleCompilerFrontier : Set where
  constructor rendered-global-scale-compiler-frontier
  field
    globalScaleInjectivityCompilerOwned : Bool
    boxResidualRetained : Bool
    uniquenessAuthorityNoLongerExternal : Bool
    concretePixelBoxToExactScalePaid : Bool
    analyticOrbitRealisationPaid : Bool

canonicalRenderedGlobalScaleCompilerFrontier :
  RenderedGlobalScaleCompilerFrontier
canonicalRenderedGlobalScaleCompilerFrontier =
  rendered-global-scale-compiler-frontier
    true true true false false
