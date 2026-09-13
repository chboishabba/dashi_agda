module DASHI.Moonshine.JInvariantRenderedIntervalOrbitRecognitionBidiExact where

open import DASHI.Core.Prelude

import DASHI.Moonshine.JInvariantOrderThreeOrbitBalancedTernaryBidiExact as Orbit
import DASHI.Moonshine.JInvariantOrderThreeSeamScaleRecognitionBidiExact as Scale
import DASHI.Core.FrontierRelationStrengthBidiExact as Relation

record RenderedAnalyticBoxCalibration
    (Rendered AnalyticPoint AnalyticBox : Set) : Set₁ where
  field
    calibrateBox : Rendered → AnalyticBox
    contains : AnalyticBox → AnalyticPoint → Set

open RenderedAnalyticBoxCalibration public

record AnalyticOrderThreeOrbitRealisation (AnalyticPoint : Set) : Set₁ where
  field
    realiseOrbitCoordinate : Orbit.RhoOrbitCoordinate → AnalyticPoint

open AnalyticOrderThreeOrbitRealisation public

record RenderedOrbitRecognition
    {Rendered AnalyticPoint AnalyticBox : Set}
    (calibration : RenderedAnalyticBoxCalibration
      Rendered AnalyticPoint AnalyticBox)
    (realisation : AnalyticOrderThreeOrbitRealisation AnalyticPoint)
    (sample : Rendered) : Set where
  constructor rendered-orbit-recognition
  field
    recognisedIndex : Nat
    recognisedContained :
      contains calibration
        (calibrateBox calibration sample)
        (realiseOrbitCoordinate realisation
          (Orbit.rhoOrbitCoordinate recognisedIndex))
    uniqueAmongOrbitFamily :
      (other : Nat) →
      contains calibration
        (calibrateBox calibration sample)
        (realiseOrbitCoordinate realisation
          (Orbit.rhoOrbitCoordinate other)) →
      other ≡ recognisedIndex

open RenderedOrbitRecognition public

recognitionToScalePoint :
  {Rendered AnalyticPoint AnalyticBox : Set} →
  {calibration : RenderedAnalyticBoxCalibration
    Rendered AnalyticPoint AnalyticBox} →
  {realisation : AnalyticOrderThreeOrbitRealisation AnalyticPoint} →
  {sample : Rendered} →
  RenderedOrbitRecognition calibration realisation sample →
  Scale.SeamScaleIndexedPoint
recognitionToScalePoint recognition =
  Scale.canonicalScalePoint (recognisedIndex recognition)

renderedIntervalRHRelation : Relation.RelationKind
renderedIntervalRHRelation = Relation.exactCertificateSchemaReuse

renderedBoxMustBeRetainedUntilUnique : Bool
renderedBoxMustBeRetainedUntilUnique = true

nearestPixelAloneEntitlesOrbitTheorem : Bool
nearestPixelAloneEntitlesOrbitTheorem = false

data RenderedIntervalOrbitResidual : Set where
  missingConcretePixelToAnalyticBoxCalibration : RenderedIntervalOrbitResidual
  missingSymbolicOrbitToAnalyticRealisation : RenderedIntervalOrbitResidual
  missingConcreteContainmentReceipts : RenderedIntervalOrbitResidual
  missingOrbitUniquenessInsideRenderedBox : RenderedIntervalOrbitResidual
  missingAnalyticStructuredJFieldAtRecognisedOrbit : RenderedIntervalOrbitResidual

record RenderedIntervalOrbitFrontier : Set where
  constructor rendered-interval-orbit-frontier
  field
    intervalValuedCalibrationTyped : Bool
    exactOrbitFamilyAvailable : Bool
    recognitionRequiresContainment : Bool
    recognitionRequiresUniqueness : Bool
    boxResidualRetained : Bool
    concreteCalibrationConstructed : Bool
    firstResidual : RenderedIntervalOrbitResidual

canonicalRenderedIntervalOrbitFrontier : RenderedIntervalOrbitFrontier
canonicalRenderedIntervalOrbitFrontier =
  rendered-interval-orbit-frontier
    true true true true true false
    missingConcretePixelToAnalyticBoxCalibration
