module DASHI.Moonshine.Monster3BFiniteSchrodingerPointProjectorEvaluationExact where

------------------------------------------------------------------------
-- EVALUATION SEMANTICS OF THE SIX-COORDINATE POINT PROJECTOR
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as V
import DASHI.Moonshine.Monster3BFiniteSchrodingerCoordinateProjectorExact as P
import DASHI.Moonshine.Monster3BFiniteSchrodingerPointProjectorExact as Point
import DASHI.Moonshine.Monster3BCyclotomicLinearAlgebraExact as L

triple : C3.Cyclotomic3 → C3.Cyclotomic3
triple a = P.tripleAmplitude a

triple2 triple3 triple4 triple5 triple6 : C3.Cyclotomic3 → C3.Cyclotomic3
triple2 a = triple (triple a)
triple3 a = triple (triple2 a)
triple4 a = triple (triple3 a)
triple5 a = triple (triple4 a)
triple6 a = triple (triple5 a)

------------------------------------------------------------------------
-- 1. Generic mismatch and zero-propagation lemmas.
------------------------------------------------------------------------

projectAmplitudeDifferent :
  (target value : Trit) →
  V.tritEqual target value ≡ false →
  (a : C3.Cyclotomic3) →
  P.projectAmplitude target value a ≡ C3.zero
projectAmplitudeDifferent neg neg () a
projectAmplitudeDifferent neg zer proof a = P.projectAmplitudeDifferentNegZer a
projectAmplitudeDifferent neg pos proof a = P.projectAmplitudeDifferentNegPos a
projectAmplitudeDifferent zer neg proof a = P.projectAmplitudeDifferentZerNeg a
projectAmplitudeDifferent zer zer () a
projectAmplitudeDifferent zer pos proof a = P.projectAmplitudeDifferentZerPos a
projectAmplitudeDifferent pos neg proof a = P.projectAmplitudeDifferentPosNeg a
projectAmplitudeDifferent pos zer proof a = P.projectAmplitudeDifferentPosZer a
projectAmplitudeDifferent pos pos () a

projectAmplitudeZero :
  (target value : Trit) → P.projectAmplitude target value C3.zero ≡ C3.zero
projectAmplitudeZero neg neg = refl
projectAmplitudeZero neg zer = refl
projectAmplitudeZero neg pos = refl
projectAmplitudeZero zer neg = refl
projectAmplitudeZero zer zer = refl
projectAmplitudeZero zer pos = refl
projectAmplitudeZero pos neg = refl
projectAmplitudeZero pos zer = refl
projectAmplitudeZero pos pos = refl

coordinateProjectorZeroAt :
  (target : Trit) → (axis : H.Axis6) →
  (f : V.SchrodingerFunction) → (x : H.X6) →
  f x ≡ C3.zero →
  P.coordinateProjector target axis f x ≡ C3.zero
coordinateProjectorZeroAt target axis f x fxZero
  rewrite P.coordinateProjectorPointwise target axis f x
        | fxZero =
  projectAmplitudeZero target (H.coordinate axis x)

coordinateProjectorDifferentAt :
  (target : Trit) → (axis : H.Axis6) →
  (f : V.SchrodingerFunction) → (x : H.X6) →
  V.tritEqual target (H.coordinate axis x) ≡ false →
  P.coordinateProjector target axis f x ≡ C3.zero
coordinateProjectorDifferentAt target axis f x different
  rewrite P.coordinateProjectorPointwise target axis f x =
  projectAmplitudeDifferent target (H.coordinate axis x) different (f x)

------------------------------------------------------------------------
-- 2. Selected point gets six successive factors of three.
------------------------------------------------------------------------

pointProjectorSelected :
  (selected : H.X6) → (f : V.SchrodingerFunction) →
  Point.pointProjector selected f selected ≡ triple6 (f selected)
pointProjectorSelected selected f
  rewrite P.coordinateProjectorPointwise (H.x5 selected) H.axis5 _ selected
        | P.projectAmplitudeSame (H.x5 selected) _
        | P.coordinateProjectorPointwise (H.x4 selected) H.axis4 _ selected
        | P.projectAmplitudeSame (H.x4 selected) _
        | P.coordinateProjectorPointwise (H.x3 selected) H.axis3 _ selected
        | P.projectAmplitudeSame (H.x3 selected) _
        | P.coordinateProjectorPointwise (H.x2 selected) H.axis2 _ selected
        | P.projectAmplitudeSame (H.x2 selected) _
        | P.coordinateProjectorPointwise (H.x1 selected) H.axis1 _ selected
        | P.projectAmplitudeSame (H.x1 selected) _
        | P.coordinateProjectorPointwise (H.x0 selected) H.axis0 f selected
        | P.projectAmplitudeSame (H.x0 selected) (f selected) = refl

------------------------------------------------------------------------
-- 3. Any explicitly separated point vanishes.  The proof follows the actual
-- projector order axis0 -> ... -> axis5 and propagates zero after the first
-- separating coordinate.
------------------------------------------------------------------------

pointProjectorOffPoint :
  (selected x : H.X6) →
  (f : V.SchrodingerFunction) →
  Point.CoordinateDifference selected x →
  Point.pointProjector selected f x ≡ C3.zero
pointProjectorOffPoint selected x f (Point.differs0 different) =
  coordinateProjectorZeroAt (H.x5 selected) H.axis5 _ x
    (coordinateProjectorZeroAt (H.x4 selected) H.axis4 _ x
      (coordinateProjectorZeroAt (H.x3 selected) H.axis3 _ x
        (coordinateProjectorZeroAt (H.x2 selected) H.axis2 _ x
          (coordinateProjectorZeroAt (H.x1 selected) H.axis1 _ x
            (coordinateProjectorDifferentAt
              (H.x0 selected) H.axis0 f x different)))))
pointProjectorOffPoint selected x f (Point.differs1 different) =
  coordinateProjectorZeroAt (H.x5 selected) H.axis5 _ x
    (coordinateProjectorZeroAt (H.x4 selected) H.axis4 _ x
      (coordinateProjectorZeroAt (H.x3 selected) H.axis3 _ x
        (coordinateProjectorZeroAt (H.x2 selected) H.axis2 _ x
          (coordinateProjectorDifferentAt
            (H.x1 selected) H.axis1
            (P.coordinateProjector (H.x0 selected) H.axis0 f) x different))))
pointProjectorOffPoint selected x f (Point.differs2 different) =
  coordinateProjectorZeroAt (H.x5 selected) H.axis5 _ x
    (coordinateProjectorZeroAt (H.x4 selected) H.axis4 _ x
      (coordinateProjectorZeroAt (H.x3 selected) H.axis3 _ x
        (coordinateProjectorDifferentAt
          (H.x2 selected) H.axis2
          (P.coordinateProjector (H.x1 selected) H.axis1
            (P.coordinateProjector (H.x0 selected) H.axis0 f)) x different)))
pointProjectorOffPoint selected x f (Point.differs3 different) =
  coordinateProjectorZeroAt (H.x5 selected) H.axis5 _ x
    (coordinateProjectorZeroAt (H.x4 selected) H.axis4 _ x
      (coordinateProjectorDifferentAt
        (H.x3 selected) H.axis3
        (P.coordinateProjector (H.x2 selected) H.axis2
          (P.coordinateProjector (H.x1 selected) H.axis1
            (P.coordinateProjector (H.x0 selected) H.axis0 f))) x different))
pointProjectorOffPoint selected x f (Point.differs4 different) =
  coordinateProjectorZeroAt (H.x5 selected) H.axis5 _ x
    (coordinateProjectorDifferentAt
      (H.x4 selected) H.axis4
      (P.coordinateProjector (H.x3 selected) H.axis3
        (P.coordinateProjector (H.x2 selected) H.axis2
          (P.coordinateProjector (H.x1 selected) H.axis1
            (P.coordinateProjector (H.x0 selected) H.axis0 f)))) x different)
pointProjectorOffPoint selected x f (Point.differs5 different) =
  coordinateProjectorDifferentAt
    (H.x5 selected) H.axis5
    (P.coordinateProjector (H.x4 selected) H.axis4
      (P.coordinateProjector (H.x3 selected) H.axis3
        (P.coordinateProjector (H.x2 selected) H.axis2
          (P.coordinateProjector (H.x1 selected) H.axis1
            (P.coordinateProjector (H.x0 selected) H.axis0 f))))) x different

record PointProjectorEvaluationBoundary : Set where
  constructor pointProjectorEvaluationBoundary
  field
    selectedPointSixTriplesProved : Bool
    explicitOffPointVanishingProved : Bool
    sixTriplesIdentifiedWith729ScalarHere : Bool
    arbitraryDistinctPointProducesDifferenceWitnessHere : Bool
    deltaLineExtractionProvedHere : Bool
    schrodingerIrreducibilityProvedHere : Bool
open PointProjectorEvaluationBoundary public

canonicalPointProjectorEvaluationBoundary : PointProjectorEvaluationBoundary
canonicalPointProjectorEvaluationBoundary =
  pointProjectorEvaluationBoundary true true false false false false
