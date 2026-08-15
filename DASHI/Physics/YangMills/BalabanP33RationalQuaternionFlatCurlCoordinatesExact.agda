module DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlCoordinatesExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
-- Kenneth G. Wilson, "Confinement of Quarks", Physical Review D 10 (1974),
-- 2445--2459. DOI: 10.1103/PhysRevD.10.2445.
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Each coordinate is normalized independently with exactly four rational
-- variables.  There is deliberately no twelve-coordinate ring solve.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlScalarExact
open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlPolynomialShapeExact

coordinateRecursionExpansion : ℚ → ℚ → ℚ → ℚ → ℚ
coordinateRecursionExpansion a b c d =
  flatRecursionShape
    (a * a) (a * b) (a * c) (a * d)
    (b * b) (b * c) (b * d)
    (c * c) (c * d) (d * d)

curlXContribution : ∀ x0 x1 x2 x3 →
  (x0 + (x1 + ((- x2) + (- x3))))
    * (x0 + (x1 + ((- x2) + (- x3))))
  ≡ coordinateRecursionExpansion x0 x1 x2 x3
curlXContribution x0 x1 x2 x3 =
  ℚRing.solve (x0 ∷ x1 ∷ x2 ∷ x3 ∷ [])

curlYContribution : ∀ y0 y1 y2 y3 →
  (y0 + (y1 + ((- y2) + (- y3))))
    * (y0 + (y1 + ((- y2) + (- y3))))
  ≡ coordinateRecursionExpansion y0 y1 y2 y3
curlYContribution y0 y1 y2 y3 =
  ℚRing.solve (y0 ∷ y1 ∷ y2 ∷ y3 ∷ [])

curlZContribution : ∀ z0 z1 z2 z3 →
  (z0 + (z1 + ((- z2) + (- z3))))
    * (z0 + (z1 + ((- z2) + (- z3))))
  ≡ coordinateRecursionExpansion z0 z1 z2 z3
curlZContribution z0 z1 z2 z3 =
  ℚRing.solve (z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])

flatCurlSquareCoordinateExpansion :
  ∀ x0 y0 z0 x1 y1 z1 x2 y2 z2 x3 y3 z3 →
  vectorNormSq
    (plaquetteCurlVector
      (vec3 x0 y0 z0) (vec3 x1 y1 z1)
      (vec3 x2 y2 z2) (vec3 x3 y3 z3))
  ≡ coordinateRecursionExpansion x0 x1 x2 x3
    + (coordinateRecursionExpansion y0 y1 y2 y3
      + coordinateRecursionExpansion z0 z1 z2 z3)
flatCurlSquareCoordinateExpansion
    x0 y0 z0 x1 y1 z1 x2 y2 z2 x3 y3 z3 =
  trans
    (ℚP.+-assoc
      ((x0 + (x1 + ((- x2) + (- x3))))
        * (x0 + (x1 + ((- x2) + (- x3)))))
      ((y0 + (y1 + ((- y2) + (- y3))))
        * (y0 + (y1 + ((- y2) + (- y3)))))
      ((z0 + (z1 + ((- z2) + (- z3))))
        * (z0 + (z1 + ((- z2) + (- z3))))))
    (cong₂ _+_
      (curlXContribution x0 x1 x2 x3)
      (cong₂ _+_
        (curlYContribution y0 y1 y2 y3)
        (curlZContribution z0 z1 z2 z3)))
