module DASHI.Physics.Closure.NSAncientCKNNestedScaleTransferNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Luis Caffarelli; Robert Kohn; Louis Nirenberg.
-- Title: "Partial regularity of suitable weak solutions of the
--         Navier-Stokes equations".
-- DOI: 10.1002/cpa.3160350604.
--
-- Authors: Tobias Barker; Christophe Prange.
-- Title: "Quantitative Regularity for the Navier-Stokes Equations Via
--         Spatial Concentration".
-- DOI: 10.1007/s00220-021-04122-x.
--
-- ROUND65 / NESTED-SCALE LOWER-BOUND NO-GO
--
-- CKN-type singularity information supplies non-small scale-invariant
-- gradient mass at suitable singular cylinders.  The KNSŠ extraction needs a
-- defect at the generally smaller velocity scale 1/M.  Merely observing that
-- the smaller cylinder is nested in the larger one cannot transfer a LOWER
-- bound inward.
--
-- Write Mass(r) for a nonnegative cumulative gradient mass and encode the
-- critical lower bound without division as
--
--   eps * r <= Mass(r).
--
-- The exact witness below places zero mass in the inner cylinder and all
-- required mass in the surrounding annulus:
--
--   Mass(inner) = 0,
--   Mass(outer) = eps * outer.
--
-- Then Mass(inner) <= Mass(outer), the outer critical lower bound is exact,
-- but the inner critical lower bound fails whenever eps, inner > 0.
-- Therefore A requires a genuine reverse-concentration / propagation theorem,
-- not positivity of |grad u|^2 and cylinder inclusion alone.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; _≤_; _<_; Positive; positive)
import Data.Rational.Properties as ℚP
open import Relation.Nullary.Negation.Core using (¬_)

innerMass : ℚ
innerMass = 0ℚ

outerMass : ℚ → ℚ → ℚ
outerMass epsilon outerRadius = epsilon * outerRadius

outerCriticalDefectExact :
  (epsilon outerRadius : ℚ) →
  epsilon * outerRadius ≡ outerMass epsilon outerRadius
outerCriticalDefectExact epsilon outerRadius = refl

innerMassNestedBelowOuter :
  (epsilon outerRadius : ℚ) →
  0ℚ ≤ epsilon →
  0ℚ ≤ outerRadius →
  innerMass ≤ outerMass epsilon outerRadius
innerMassNestedBelowOuter epsilon outerRadius epsilonNN radiusNN =
  let
    instance epsilonNonnegative = positiveOrZero epsilon epsilonNN
    instance radiusNonnegative = positiveOrZero outerRadius radiusNN
  in
  ℚP.nonNegative⁻¹ (epsilon * outerRadius)
  where
    positiveOrZero : (x : ℚ) → 0ℚ ≤ x → Data.Rational.Base.NonNegative x
    positiveOrZero x proof = Data.Rational.Base.nonNegative proof

innerCriticalDefectFails :
  (epsilon innerRadius : ℚ) →
  0ℚ < epsilon →
  0ℚ < innerRadius →
  ¬ (epsilon * innerRadius ≤ innerMass)
innerCriticalDefectFails epsilon innerRadius epsilonPositive innerPositive proposed =
  let
    instance innerPos : Positive innerRadius
        innerPos = positive innerPositive

    epsilonTimesInnerPositive : 0ℚ < epsilon * innerRadius
    epsilonTimesInnerPositive =
      ℚP.*-monoʳ-<-pos innerRadius epsilonPositive

    proposedNormalized : epsilon * innerRadius ≤ 0ℚ
    proposedNormalized = proposed
  in
  ℚP.<-irrefl 0ℚ
    (ℚP.<-≤-trans epsilonTimesInnerPositive proposedNormalized)

-- This is deliberately a measure-theoretic falsifier, not a Navier-Stokes
-- counterexample.  It proves exactly that nesting/positivity cannot be the
-- missing SingularScaleVelocityScaleMatching argument.
