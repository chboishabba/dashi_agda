module DASHI.Physics.Closure.NSTriadKNR290CanonicalOneStepG2PathExact where

------------------------------------------------------------------------
-- B / G2 CANONICAL ONE-STEP PATH REALIZATION
--
-- The previous complex-path theorem accepted real/imaginary finite paths as
-- inputs.  Their existence is not a genuine analytic debt: for any literal
-- X+/X- pair the endpoint differences themselves form canonical singleton
-- paths.
--
-- This pays the path-CONSTRUCTION seam exactly.  It does not claim the
-- singleton increment is already a physical derivative.  The surviving G2
-- theorem is therefore precisely:
--
--   literal state increment
--       -> displacement-scaled physical gradient / difference quotient.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (1ℚ)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNR571HermitianScalarizedOppositePairExact as G0
import DASHI.Physics.Closure.NSTriadKNR290ComplexPathDifferenceG2Exact as G2
import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram
import DASHI.Physics.Closure.NSTriadKNLuoFinitePathDifferenceDiffusionExact as Path

F = G0.Weld.F

singletonPath : Gram.Vec3 → Agda.Builtin.List.List Gram.Vec3
singletonPath increment = increment ∷ []

singletonPathEndpoint :
  (increment : Gram.Vec3) →
  Path.pathEndpointDifference (singletonPath increment) ≡ increment
singletonPathEndpoint (Gram.vec3 ix iy iz) = refl

canonicalOneStepComplexPath :
  (plus minus : C3.Complex3 F) →
  G2.ComplexPathRealization plus minus
canonicalOneStepComplexPath plus minus = record
  { G2.realPath =
      singletonPath (G2.differenceRealVec3 plus minus)
  ; G2.imagPath =
      singletonPath (G2.differenceImagVec3 plus minus)
  ; G2.realEndpoint =
      singletonPathEndpoint (G2.differenceRealVec3 plus minus)
  ; G2.imagEndpoint =
      singletonPathEndpoint (G2.differenceImagVec3 plus minus)
  }

canonicalOneStepComplexPathExists : Bool
canonicalOneStepComplexPathExists = true

g2PathExistenceIsNoLongerAnInput : Bool
g2PathExistenceIsNoLongerAnInput = true

physicalIncrementToGradientClosedHere : Bool
physicalIncrementToGradientClosedHere = false

scaleUniformGradientCoefficientClosedHere : Bool
scaleUniformGradientCoefficientClosedHere = false

clayPromotion : Bool
clayPromotion = false

canonicalOneStepComplexPathExistsIsTrue :
  canonicalOneStepComplexPathExists ≡ true
canonicalOneStepComplexPathExistsIsTrue = refl

g2PathExistenceIsNoLongerAnInputIsTrue :
  g2PathExistenceIsNoLongerAnInput ≡ true
g2PathExistenceIsNoLongerAnInputIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
