{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTSourceAmplitudeDrivenIsraelKottlerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Foundations.GRQFTRationalSquareIsraelDesignExact as Israel
import DASHI.Physics.Foundations.GRQFTKottlerRepulsionParameterWindowExact as Window

------------------------------------------------------------------------
-- SOURCE-AMPLITUDE-DRIVEN ISRAEL / KOTTLER INVERSION
--
-- The earlier exact fixtures 21/64 and 19/48 are convenient witnesses, not
-- physical values that CMP119 must magically reproduce.  For a chosen shell
-- radius R and exterior lapse root y, use the source-produced scaled exterior
-- vacuum amplitude
--
--     L_out = Lambda_out R^3
--
-- and solve the Kottler lapse equation for the mass:
--
--     6 M = 3 R (1-y^2) - L_out.
--
-- This is denominator-free and therefore does not manufacture a nonzero-radius
-- cancellation.  The source interior amplitude is admitted by the equally
-- denominator-free square-lapse equation
--
--     Lambda_in R^2 = 3(1-x^2).
--
-- All Israel shell stresses and Kottler margins are then existing functions of
-- (M,R,x,y).  Thus source amplitudes need satisfy an OPEN admissibility region;
-- they do not need to equal one preselected rational fixture.
------------------------------------------------------------------------

three : ℚ
three = Int.+ 3 / 1

six : ℚ
six = Int.+ 6 / 1

threeHalves : ℚ
threeHalves = Int.+ 3 / 2

massFromExteriorAmplitude :
  (radius exteriorLapseRoot exteriorScaledAmplitude : ℚ) → ℚ
massFromExteriorAmplitude radius y scaledLambda =
  (three * radius * (Int.+ 1 / 1 - y * y) - scaledLambda) / six

interiorAmplitudeEquation :
  (radius interiorLapseRoot interiorAmplitude : ℚ) → ℚ
interiorAmplitudeEquation radius x lambdaIn =
  lambdaIn * radius * radius
  - three * (Int.+ 1 / 1 - x * x)

exteriorAmplitudeEquation :
  (radius exteriorLapseRoot exteriorScaledAmplitude : ℚ) → ℚ
exteriorAmplitudeEquation radius y scaledLambda =
  six * massFromExteriorAmplitude radius y scaledLambda
  - (three * radius * (Int.+ 1 / 1 - y * y) - scaledLambda)

exteriorAmplitudeInversion :
  ∀ radius y scaledLambda →
  exteriorAmplitudeEquation radius y scaledLambda ≡ Int.+ 0 / 1
exteriorAmplitudeInversion radius y scaledLambda =
  solve (radius ∷ y ∷ scaledLambda ∷ [])

sourceExteriorScaledAmplitude :
  (radius sourceLambdaOut : ℚ) → ℚ
sourceExteriorScaledAmplitude radius sourceLambdaOut =
  sourceLambdaOut * radius * radius * radius

sourceInteriorScaledAmplitude :
  (radius sourceLambdaIn : ℚ) → ℚ
sourceInteriorScaledAmplitude radius sourceLambdaIn =
  sourceLambdaIn * radius * radius

sourceInteriorRootResidual :
  (radius x sourceLambdaIn : ℚ) → ℚ
sourceInteriorRootResidual radius x sourceLambdaIn =
  sourceInteriorScaledAmplitude radius sourceLambdaIn
  - three * (Int.+ 1 / 1 - x * x)

sourceExteriorMass :
  (radius y sourceLambdaOut : ℚ) → ℚ
sourceExteriorMass radius y sourceLambdaOut =
  massFromExteriorAmplitude radius y
    (sourceExteriorScaledAmplitude radius sourceLambdaOut)

------------------------------------------------------------------------
-- Once M is solved from the exterior source amplitude, the two Kottler window
-- margins simplify exactly.  Positivity/order remains a separate source-data
-- question; the algebra is no longer open.
------------------------------------------------------------------------

sourceDrivenOutwardMarginIdentity :
  ∀ radius y scaledLambda →
  Window.outwardAccelerationMargin
    (massFromExteriorAmplitude radius y scaledLambda)
    scaledLambda
  ≡ threeHalves
      * (scaledLambda - radius * (Int.+ 1 / 1 - y * y))
sourceDrivenOutwardMarginIdentity radius y scaledLambda =
  solve (radius ∷ y ∷ scaledLambda ∷ [])

sourceDrivenStaticMarginIdentity :
  ∀ radius y scaledLambda →
  Window.staticPatchMargin
    (massFromExteriorAmplitude radius y scaledLambda)
    radius scaledLambda
  ≡ three * radius * y * y
sourceDrivenStaticMarginIdentity radius y scaledLambda =
  solve (radius ∷ y ∷ scaledLambda ∷ [])

sourceDrivenSurfaceSigma :
  (radius x y : ℚ) → ℚ
sourceDrivenSurfaceSigma = Israel.surfaceSigma8

sourceDrivenSurfacePressure :
  (radius x y scaledLambda : ℚ) → ℚ
sourceDrivenSurfacePressure radius x y scaledLambda =
  Israel.surfacePressure8
    (massFromExteriorAmplitude radius y scaledLambda)
    radius x y

sourceDrivenNECDECMargin :
  (radius x y scaledLambda : ℚ) → ℚ
sourceDrivenNECDECMargin radius x y scaledLambda =
  Israel.necDecMarginCleared
    (massFromExteriorAmplitude radius y scaledLambda)
    radius x y

sourceDrivenSECViolationMargin :
  (radius x y scaledLambda : ℚ) → ℚ
sourceDrivenSECViolationMargin radius x y scaledLambda =
  Israel.secViolationMarginCleared
    (massFromExteriorAmplitude radius y scaledLambda)
    radius x y

sourceDrivenPressureTensionMargin :
  (radius x y scaledLambda : ℚ) → ℚ
sourceDrivenPressureTensionMargin radius x y scaledLambda =
  Israel.pressureTensionMarginCleared
    (massFromExteriorAmplitude radius y scaledLambda)
    radius x y

record SourceAmplitudeDrivenIsraelKottlerBoundary : Set where
  constructor source-amplitude-driven-israel-kottler-boundary
  field
    exteriorMassSolvedAlgebraically : Bool
    exteriorAmplitudeInversionExact : Bool
    interiorAmplitudeUsesSquareLapseEquation : Bool
    staticMarginReducedToPositiveGeometryProduct : Bool
    outwardMarginReducedToOneSourceInequality : Bool
    shellStressUsesExistingIsraelCompiler : Bool
    sourceAmplitudesNeedNotEqualFixtureFractions : Bool
    remainingSourceLeafIsAdmissibilityNotMagicValues : Bool

canonicalSourceAmplitudeDrivenIsraelKottlerBoundary :
  SourceAmplitudeDrivenIsraelKottlerBoundary
canonicalSourceAmplitudeDrivenIsraelKottlerBoundary =
  source-amplitude-driven-israel-kottler-boundary
    true true true true true true true true
