module DASHI.Physics.Closure.NSTriadKNR290ComplexPathDifferenceG2Exact where

------------------------------------------------------------------------
-- B / G2: SIX-REAL-COORDINATE PATH DIFFERENCE BOUND
--
-- The finite-path donor is a real R^3 estimate.  The literal R290/G0' state is
-- complex C^3, i.e. six rational coordinates.  This owner performs the exact
-- same-object split:
--
--   ||X_+ - X_-||_{C^3}^2
--     = ||Re(X_+ - X_-)||_{R^3}^2
--       + ||Im(X_+ - X_-)||_{R^3}^2.
--
-- If two finite real paths have those two endpoint differences, the existing
-- path Jensen theorem gives
--
--   ||X_+ - X_-||^2
--     <= n_Re E_Re + n_Im E_Im.
--
-- No square root, shell count, fibre cardinality or multiplier estimate is
-- introduced.  The remaining physical G2 seam is now only the construction of
-- these paths from the actual paired displacement and their scale-uniform
-- gradient-energy estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _-_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram
import DASHI.Physics.Closure.NSTriadKNLuoFinitePathDifferenceDiffusionExact as Path
import DASHI.Physics.Closure.NSTriadKNR571HermitianScalarizedOppositePairExact as G0

F = G0.Weld.F

realPartVec3 : C3.Complex3 F → Gram.Vec3
realPartVec3 value =
  Gram.vec3
    (C3.real (C3.x value))
    (C3.real (C3.y value))
    (C3.real (C3.z value))

imagPartVec3 : C3.Complex3 F → Gram.Vec3
imagPartVec3 value =
  Gram.vec3
    (C3.imaginary (C3.x value))
    (C3.imaginary (C3.y value))
    (C3.imaginary (C3.z value))

differenceRealVec3 :
  C3.Complex3 F → C3.Complex3 F → Gram.Vec3
differenceRealVec3 plus minus =
  Gram.vec3
    (C3.real (C3.x plus) - C3.real (C3.x minus))
    (C3.real (C3.y plus) - C3.real (C3.y minus))
    (C3.real (C3.z plus) - C3.real (C3.z minus))

differenceImagVec3 :
  C3.Complex3 F → C3.Complex3 F → Gram.Vec3
differenceImagVec3 plus minus =
  Gram.vec3
    (C3.imaginary (C3.x plus) - C3.imaginary (C3.x minus))
    (C3.imaginary (C3.y plus) - C3.imaginary (C3.y minus))
    (C3.imaginary (C3.z plus) - C3.imaginary (C3.z minus))

complexDifferenceNormSplit :
  (plus minus : C3.Complex3 F) →
  L2.complex3NormSquared (C3.complex3Subtract plus minus)
  ≡
  Gram.normSquared (differenceRealVec3 plus minus)
  + Gram.normSquared (differenceImagVec3 plus minus)
complexDifferenceNormSplit
    (C3.complex3
      (C3.complex pxr pxi) (C3.complex pyr pyi) (C3.complex pzr pzi))
    (C3.complex3
      (C3.complex mxr mxi) (C3.complex myr myi) (C3.complex mzr mzi)) =
  solve
    ( pxr ∷ pxi ∷ pyr ∷ pyi ∷ pzr ∷ pzi
    ∷ mxr ∷ mxi ∷ myr ∷ myi ∷ mzr ∷ mzi
    ∷ [])

record ComplexPathRealization
    (plus minus : C3.Complex3 F) : Set where
  field
    realPath : List Gram.Vec3
    imagPath : List Gram.Vec3

    realEndpoint :
      Path.pathEndpointDifference realPath
      ≡ differenceRealVec3 plus minus

    imagEndpoint :
      Path.pathEndpointDifference imagPath
      ≡ differenceImagVec3 plus minus

open ComplexPathRealization public

complexPathDifferenceBound :
  (plus minus : C3.Complex3 F) →
  (R : ComplexPathRealization plus minus) →
  L2.complex3NormSquared (C3.complex3Subtract plus minus)
  ≤
    Path.pathStepCount (realPath R) * Path.pathGradientEnergy (realPath R)
    +
    Path.pathStepCount (imagPath R) * Path.pathGradientEnergy (imagPath R)
complexPathDifferenceBound plus minus R =
  let
    realBound =
      Path.finitePathDifferenceBelowGradientEnergy (realPath R)
    imagBound =
      Path.finitePathDifferenceBelowGradientEnergy (imagPath R)

    summed = ℚP.+-mono-≤ realBound imagBound

    endpointRewrite :
      Gram.normSquared (Path.pathEndpointDifference (realPath R))
      + Gram.normSquared (Path.pathEndpointDifference (imagPath R))
      ≡
      Gram.normSquared (differenceRealVec3 plus minus)
      + Gram.normSquared (differenceImagVec3 plus minus)
    endpointRewrite
      rewrite realEndpoint R | imagEndpoint R = refl
  in
  subst
    (λ left →
      left
      ≤
        Path.pathStepCount (realPath R) * Path.pathGradientEnergy (realPath R)
        +
        Path.pathStepCount (imagPath R) * Path.pathGradientEnergy (imagPath R))
    (complexDifferenceNormSplit plus minus)
    (subst
      (λ left →
        left
        ≤
          Path.pathStepCount (realPath R) * Path.pathGradientEnergy (realPath R)
          +
          Path.pathStepCount (imagPath R) * Path.pathGradientEnergy (imagPath R))
      endpointRewrite
      summed)

r290ComplexStateDifferenceFinitePathBoundClosed : Bool
r290ComplexStateDifferenceFinitePathBoundClosed = true

sixRealCoordinatesAllPaid : Bool
sixRealCoordinatesAllPaid = true

physicalPairedDisplacementBuildsPathsClosedHere : Bool
physicalPairedDisplacementBuildsPathsClosedHere = false

scaleUniformGradientCoefficientClosedHere : Bool
scaleUniformGradientCoefficientClosedHere = false

cutoffUniformG2ClosedHere : Bool
cutoffUniformG2ClosedHere = false

clayPromotion : Bool
clayPromotion = false

r290ComplexStateDifferenceFinitePathBoundClosedIsTrue :
  r290ComplexStateDifferenceFinitePathBoundClosed ≡ true
r290ComplexStateDifferenceFinitePathBoundClosedIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
