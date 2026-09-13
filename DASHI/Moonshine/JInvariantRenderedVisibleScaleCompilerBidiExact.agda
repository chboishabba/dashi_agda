module DASHI.Moonshine.JInvariantRenderedVisibleScaleCompilerBidiExact where

------------------------------------------------------------------------
-- RENDERED BOX -> VISIBLE SCALE -> UNIQUE k COMPILER
--
-- For the current source-aligned order-three beam, the candidate fibre is
-- k=0..7 and the exact scale code is injective:
--
--   1,3,7,13,21,31,43,57.
--
-- A concrete image calibration therefore does not need to supply a separate
-- uniqueness theorem for k.  It only has to retain its analytic uncertainty
-- box and certify which exact visible scale every contained visible candidate
-- has.  Injectivity then compiles uniqueness.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.JInvariantOrderThreeOrbitBalancedTernaryBidiExact as Orbit
import DASHI.Moonshine.JInvariantOrderThreeSeamScaleRecognitionBidiExact as Scale
import DASHI.Moonshine.JInvariantOrderThreeVisibleScaleUniquenessBidiExact as Visible
import DASHI.Moonshine.JInvariantRenderedIntervalOrbitRecognitionBidiExact as Rendered
import DASHI.Core.FrontierRelationStrengthBidiExact as Relation

------------------------------------------------------------------------
-- 1. A rendered-box scale certificate retains the box as residual data.
------------------------------------------------------------------------

record RenderedVisibleScaleBoxCertificate
    {RenderedPoint AnalyticPoint AnalyticBox : Set}
    (calibration : Rendered.RenderedAnalyticBoxCalibration
      RenderedPoint AnalyticPoint AnalyticBox)
    (realisation : Rendered.AnalyticOrderThreeOrbitRealisation AnalyticPoint)
    (sample : RenderedPoint) : Set where
  constructor rendered-visible-scale-box-certificate
  field
    candidate : Visible.VisibleEightIndex
    measuredScale : Nat
    scaleMatchesCandidate :
      measuredScale ≡ Visible.visibleScale candidate
    candidateContained :
      Rendered.contains calibration
        (Rendered.calibrateBox calibration sample)
        (Rendered.realiseOrbitCoordinate realisation
          (Orbit.rhoOrbitCoordinate (Visible.visibleIndex candidate)))
    everyContainedVisibleCandidateHasMeasuredScale :
      (other : Visible.VisibleEightIndex) →
      Rendered.contains calibration
        (Rendered.calibrateBox calibration sample)
        (Rendered.realiseOrbitCoordinate realisation
          (Orbit.rhoOrbitCoordinate (Visible.visibleIndex other))) →
      Visible.visibleScale other ≡ measuredScale

open RenderedVisibleScaleBoxCertificate public

------------------------------------------------------------------------
-- 2. Scale injectivity makes visible-family uniqueness compiler-owned.
------------------------------------------------------------------------

containedVisibleCandidateIsUnique :
  {RenderedPoint AnalyticPoint AnalyticBox : Set} →
  {calibration : Rendered.RenderedAnalyticBoxCalibration
    RenderedPoint AnalyticPoint AnalyticBox} →
  {realisation : Rendered.AnalyticOrderThreeOrbitRealisation AnalyticPoint} →
  {sample : RenderedPoint} →
  (certificate : RenderedVisibleScaleBoxCertificate
    calibration realisation sample) →
  (other : Visible.VisibleEightIndex) →
  Rendered.contains calibration
    (Rendered.calibrateBox calibration sample)
    (Rendered.realiseOrbitCoordinate realisation
      (Orbit.rhoOrbitCoordinate (Visible.visibleIndex other))) →
  other ≡ candidate certificate
containedVisibleCandidateIsUnique certificate other contained =
  Visible.visibleScaleInjective
    other
    (candidate certificate)
    (trans
      (everyContainedVisibleCandidateHasMeasuredScale
        certificate other contained)
      (scaleMatchesCandidate certificate))

------------------------------------------------------------------------
-- 3. Restricted rendered recognition packet for the actual visible family.
------------------------------------------------------------------------

record RenderedVisibleEightRecognition
    {RenderedPoint AnalyticPoint AnalyticBox : Set}
    (calibration : Rendered.RenderedAnalyticBoxCalibration
      RenderedPoint AnalyticPoint AnalyticBox)
    (realisation : Rendered.AnalyticOrderThreeOrbitRealisation AnalyticPoint)
    (sample : RenderedPoint) : Set where
  constructor rendered-visible-eight-recognition
  field
    recognisedVisible : Visible.VisibleEightIndex
    recognisedScale : Nat
    recognisedScaleExact :
      recognisedScale ≡ Visible.visibleScale recognisedVisible
    recognisedContained :
      Rendered.contains calibration
        (Rendered.calibrateBox calibration sample)
        (Rendered.realiseOrbitCoordinate realisation
          (Orbit.rhoOrbitCoordinate (Visible.visibleIndex recognisedVisible)))
    uniqueInsideVisibleFamily :
      (other : Visible.VisibleEightIndex) →
      Rendered.contains calibration
        (Rendered.calibrateBox calibration sample)
        (Rendered.realiseOrbitCoordinate realisation
          (Orbit.rhoOrbitCoordinate (Visible.visibleIndex other))) →
      other ≡ recognisedVisible

open RenderedVisibleEightRecognition public

compileRenderedVisibleEightRecognition :
  {RenderedPoint AnalyticPoint AnalyticBox : Set} →
  {calibration : Rendered.RenderedAnalyticBoxCalibration
    RenderedPoint AnalyticPoint AnalyticBox} →
  {realisation : Rendered.AnalyticOrderThreeOrbitRealisation AnalyticPoint} →
  {sample : RenderedPoint} →
  RenderedVisibleScaleBoxCertificate calibration realisation sample →
  RenderedVisibleEightRecognition calibration realisation sample
compileRenderedVisibleEightRecognition certificate =
  rendered-visible-eight-recognition
    (candidate certificate)
    (measuredScale certificate)
    (scaleMatchesCandidate certificate)
    (candidateContained certificate)
    (containedVisibleCandidateIsUnique certificate)

------------------------------------------------------------------------
-- 4. Once recognised, the existing exact seam-scale / modular-word lane takes
--    over.  No second scale notion is introduced.
------------------------------------------------------------------------

recognisedVisibleIndex :
  {RenderedPoint AnalyticPoint AnalyticBox : Set} →
  {calibration : Rendered.RenderedAnalyticBoxCalibration
    RenderedPoint AnalyticPoint AnalyticBox} →
  {realisation : Rendered.AnalyticOrderThreeOrbitRealisation AnalyticPoint} →
  {sample : RenderedPoint} →
  RenderedVisibleEightRecognition calibration realisation sample →
  Nat
recognisedVisibleIndex recognition =
  Visible.visibleIndex (recognisedVisible recognition)

recognitionToScalePoint :
  {RenderedPoint AnalyticPoint AnalyticBox : Set} →
  {calibration : Rendered.RenderedAnalyticBoxCalibration
    RenderedPoint AnalyticPoint AnalyticBox} →
  {realisation : Rendered.AnalyticOrderThreeOrbitRealisation AnalyticPoint} →
  {sample : RenderedPoint} →
  RenderedVisibleEightRecognition calibration realisation sample →
  Scale.SeamScaleIndexedPoint
recognitionToScalePoint recognition =
  Scale.canonicalScalePoint (recognisedVisibleIndex recognition)

------------------------------------------------------------------------
-- 5. RH-style residual governance / frontier.
------------------------------------------------------------------------

renderedVisibleScaleRelation : Relation.RelationKind
renderedVisibleScaleRelation = Relation.exactCertificateSchemaReuse

record RenderedVisibleScaleCompilerFrontier : Set where
  constructor rendered-visible-scale-compiler-frontier
  field
    boxResidualRetained : Bool
    visibleScaleCodeInjective : Bool
    uniquenessFromScaleCompilerOwned : Bool
    concretePixelBoxToExactScalePaid : Bool
    unrestrictedNatOrbitRecognitionClaimed : Bool

canonicalRenderedVisibleScaleCompilerFrontier :
  RenderedVisibleScaleCompilerFrontier
canonicalRenderedVisibleScaleCompilerFrontier =
  rendered-visible-scale-compiler-frontier
    true true true false false
