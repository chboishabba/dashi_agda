module DASHI.Physics.Closure.NSTriadKNEuclideanCanonicalLerayProjectionExact where

------------------------------------------------------------------------
-- A / CANONICAL CONTINUOUS LERAY PROJECTOR ON THE PUNCTURED CARRIER
--
-- The Euclidean heat-rate owner already carries
--
--   0 < |xi|^2
--
-- on PuncturedEuclideanFrequency.  Therefore the inverse required by the
-- continuous Leray formula is not an extra authority: it is the canonical
-- Bishop inverse of |xi|^2.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal
import DASHI.Physics.Closure.NSTriadKNEuclideanViscousHeatRateExact as Heat
import DASHI.Physics.Closure.NSTriadKNEuclideanBishopLerayPythagorasExact as Leray

canonicalInverseNormSquared :
  Heat.PuncturedEuclideanFrequency →
  BishopReal.ℝ
canonicalInverseNormSquared point =
  BishopInverse._⁻¹
    (Heat.frequencyNormSquared (Heat.frequency point))
    (Reciprocal.xNonzero (Heat.normSquaredPositive point))

canonicalLerayInverse :
  (point : Heat.PuncturedEuclideanFrequency) →
  Leray.ContinuousLerayInverse (Heat.frequency point)
canonicalLerayInverse point =
  Leray.continuous-leray-inverse
    (canonicalInverseNormSquared point)
    (BishopInverse.*-inverseˡ
      (Heat.frequencyNormSquared (Heat.frequency point))
      (Reciprocal.xNonzero (Heat.normSquaredPositive point)))
    (BishopP.pos⇒nonNeg
      (BishopP.0<x⇒posx
        (BishopInverse.0<x⇒0<x⁻¹
          (Reciprocal.xNonzero (Heat.normSquaredPositive point))
          (Heat.normSquaredPositive point))))

canonicalLerayInverseClosed : Bool
canonicalLerayInverseClosed = true

externalInverseNormAuthorityRequired : Bool
externalInverseNormAuthorityRequired = false

clayPromotion : Bool
clayPromotion = false

canonicalLerayInverseClosedIsTrue :
  canonicalLerayInverseClosed ≡ true
canonicalLerayInverseClosedIsTrue = refl

externalInverseNormAuthorityRequiredIsFalse :
  externalInverseNormAuthorityRequired ≡ false
externalInverseNormAuthorityRequiredIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
