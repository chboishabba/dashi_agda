module DASHI.Moonshine.Monster3BFiniteSchrodingerPointProjectorExact where

------------------------------------------------------------------------
-- SIX-COORDINATE POINT PROJECTOR ON X6
--
-- Compose the six derived coordinate Fourier projectors.  This is a genuine
-- Heisenberg-generated point projector: no arbitrary support selector enters
-- the invariant-subspace proof.  Pointwise extraction and scalar
-- normalisation remain separately typed below.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as V
import DASHI.Moonshine.Monster3BFiniteSchrodingerCoordinateProjectorExact as P

pointProjector : H.X6 → V.SchrodingerFunction → V.SchrodingerFunction
pointProjector selected f =
  P.coordinateProjector (H.x5 selected) H.axis5
    (P.coordinateProjector (H.x4 selected) H.axis4
      (P.coordinateProjector (H.x3 selected) H.axis3
        (P.coordinateProjector (H.x2 selected) H.axis2
          (P.coordinateProjector (H.x1 selected) H.axis1
            (P.coordinateProjector (H.x0 selected) H.axis0 f)))))

pointProjectorPreservesInvariantSubspace :
  {Member : V.SchrodingerFunction → Set} →
  V.HeisenbergInvariantSubspace Member →
  (selected : H.X6) → (f : V.SchrodingerFunction) → Member f →
  Member (pointProjector selected f)
pointProjectorPreservesInvariantSubspace {Member} inv selected f member =
  P.projectorPreservesInvariantSubspace inv (H.x5 selected) H.axis5 _
    (P.projectorPreservesInvariantSubspace inv (H.x4 selected) H.axis4 _
      (P.projectorPreservesInvariantSubspace inv (H.x3 selected) H.axis3 _
        (P.projectorPreservesInvariantSubspace inv (H.x2 selected) H.axis2 _
          (P.projectorPreservesInvariantSubspace inv (H.x1 selected) H.axis1 _
            (P.projectorPreservesInvariantSubspace inv (H.x0 selected) H.axis0 f member)))))

------------------------------------------------------------------------
-- Explicit six-coordinate difference witness for later off-point vanishing.
-- This is stronger and more useful than a bare Boolean inequality because it
-- tells the projector proof exactly which character coordinate separates the
-- two points.
------------------------------------------------------------------------

data CoordinateDifference : H.X6 → H.X6 → Set where
  differs0 : {s x : H.X6} → V.tritEqual (H.x0 s) (H.x0 x) ≡ false →
    CoordinateDifference s x
  differs1 : {s x : H.X6} → V.tritEqual (H.x1 s) (H.x1 x) ≡ false →
    CoordinateDifference s x
  differs2 : {s x : H.X6} → V.tritEqual (H.x2 s) (H.x2 x) ≡ false →
    CoordinateDifference s x
  differs3 : {s x : H.X6} → V.tritEqual (H.x3 s) (H.x3 x) ≡ false →
    CoordinateDifference s x
  differs4 : {s x : H.X6} → V.tritEqual (H.x4 s) (H.x4 x) ≡ false →
    CoordinateDifference s x
  differs5 : {s x : H.X6} → V.tritEqual (H.x5 s) (H.x5 x) ≡ false →
    CoordinateDifference s x

record PointProjectorBoundary : Set where
  constructor pointProjectorBoundary
  field
    sixCoordinateProjectorConstructed : Bool
    derivedOnlyFromModulationsAndLinearClosure : Bool
    invariantSubspaceClosureProved : Bool
    explicitCoordinateDifferenceWitnessAvailable : Bool
    selectedPointCoefficient729ProvedHere : Bool
    offPointVanishingProvedHere : Bool
    nonzeroCoefficientNormalisedToDeltaHere : Bool
    schrodingerIrreducibilityProvedHere : Bool
open PointProjectorBoundary public

canonicalPointProjectorBoundary : PointProjectorBoundary
canonicalPointProjectorBoundary =
  pointProjectorBoundary true true true true false false false false
