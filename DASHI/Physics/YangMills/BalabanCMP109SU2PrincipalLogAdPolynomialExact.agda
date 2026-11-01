module DASHI.Physics.YangMills.BalabanCMP109SU2PrincipalLogAdPolynomialExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- The axis form of the SU(2) principal-log Jacobian is ideal for coercivity,
-- but the normalized axis n = X/|X| is the wrong object for continuity at
-- X = 0.  This module gives the complementary regular representation
--
--     J_X = I + c1 ad_X + c2 ad_X^2,
--     ad_X(v) = X x v,
--
-- entirely in polynomial coordinates.  It proves the vector triple-product
-- identity, the exact first and second ad-difference identities, and the exact
-- equivalence with the existing axis representation whenever X = r n and n is
-- unit.  No division by r occurs anywhere.
--
-- For the inverse-dexp convention used downstream c1 is the fixed signed half
-- coefficient and c2 is the even Bernoulli coefficient beta(r).  Thus all
-- nontrivial regularity is isolated in c2, while the operator geometry remains
-- polynomial through the chart origin.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109SU2PrincipalLogJacobianStructureExact as Axis

ad0 : ℚ → ℚ → ℚ → ℚ → ℚ
ad0 x1 x2 v1 v2 = x1 * v2 - x2 * v1

ad1 : ℚ → ℚ → ℚ → ℚ → ℚ
ad1 x0 x2 v0 v2 = x2 * v0 - x0 * v2

ad2 : ℚ → ℚ → ℚ → ℚ → ℚ
ad2 x0 x1 v0 v1 = x0 * v1 - x1 * v0

adSquare0 : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
adSquare0 x0 x1 x2 v0 v1 v2 =
  ad0 x1 x2
    (ad1 x0 x2 v0 v2)
    (ad2 x0 x1 v0 v1)

adSquare1 : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
adSquare1 x0 x1 x2 v0 v1 v2 =
  ad1 x0 x2
    (ad0 x1 x2 v1 v2)
    (ad2 x0 x1 v0 v1)

adSquare2 : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
adSquare2 x0 x1 x2 v0 v1 v2 =
  ad2 x0 x1
    (ad0 x1 x2 v1 v2)
    (ad1 x0 x2 v0 v2)

adSquare0TripleProduct : ∀ x0 x1 x2 v0 v1 v2 →
  adSquare0 x0 x1 x2 v0 v1 v2
  ≡ x0 * Axis.dot3 x0 x1 x2 v0 v1 v2
      - Axis.normSq3 x0 x1 x2 * v0
adSquare0TripleProduct x0 x1 x2 v0 v1 v2 =
  ℚRing.solve-∀ x0 x1 x2 v0 v1 v2

adSquare1TripleProduct : ∀ x0 x1 x2 v0 v1 v2 →
  adSquare1 x0 x1 x2 v0 v1 v2
  ≡ x1 * Axis.dot3 x0 x1 x2 v0 v1 v2
      - Axis.normSq3 x0 x1 x2 * v1
adSquare1TripleProduct x0 x1 x2 v0 v1 v2 =
  ℚRing.solve-∀ x0 x1 x2 v0 v1 v2

adSquare2TripleProduct : ∀ x0 x1 x2 v0 v1 v2 →
  adSquare2 x0 x1 x2 v0 v1 v2
  ≡ x2 * Axis.dot3 x0 x1 x2 v0 v1 v2
      - Axis.normSq3 x0 x1 x2 * v2
adSquare2TripleProduct x0 x1 x2 v0 v1 v2 =
  ℚRing.solve-∀ x0 x1 x2 v0 v1 v2

principalLogAdPolynomial0 :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
principalLogAdPolynomial0 c1 c2 x0 x1 x2 v0 v1 v2 =
  v0 + c1 * ad0 x1 x2 v1 v2
     + c2 * adSquare0 x0 x1 x2 v0 v1 v2

principalLogAdPolynomial1 :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
principalLogAdPolynomial1 c1 c2 x0 x1 x2 v0 v1 v2 =
  v1 + c1 * ad1 x0 x2 v0 v2
     + c2 * adSquare1 x0 x1 x2 v0 v1 v2

principalLogAdPolynomial2 :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
principalLogAdPolynomial2 c1 c2 x0 x1 x2 v0 v1 v2 =
  v2 + c1 * ad2 x0 x1 v0 v1
     + c2 * adSquare2 x0 x1 x2 v0 v1 v2

------------------------------------------------------------------------
-- Difference identities.  These are the algebraic heart of the local modulus:
-- ad_X-ad_Y = ad_(X-Y), and
-- ad_X^2-ad_Y^2 = ad_X(ad_X-ad_Y)+(ad_X-ad_Y)ad_Y.
------------------------------------------------------------------------

adDifference0 : ∀ x1 x2 y1 y2 v1 v2 →
  ad0 x1 x2 v1 v2 - ad0 y1 y2 v1 v2
  ≡ ad0 (x1 - y1) (x2 - y2) v1 v2
adDifference0 x1 x2 y1 y2 v1 v2 =
  ℚRing.solve-∀ x1 x2 y1 y2 v1 v2

adDifference1 : ∀ x0 x2 y0 y2 v0 v2 →
  ad1 x0 x2 v0 v2 - ad1 y0 y2 v0 v2
  ≡ ad1 (x0 - y0) (x2 - y2) v0 v2
adDifference1 x0 x2 y0 y2 v0 v2 =
  ℚRing.solve-∀ x0 x2 y0 y2 v0 v2

adDifference2 : ∀ x0 x1 y0 y1 v0 v1 →
  ad2 x0 x1 v0 v1 - ad2 y0 y1 v0 v1
  ≡ ad2 (x0 - y0) (x1 - y1) v0 v1
adDifference2 x0 x1 y0 y1 v0 v1 =
  ℚRing.solve-∀ x0 x1 y0 y1 v0 v1

adSquareDifference0 : ∀ x0 x1 x2 y0 y1 y2 v0 v1 v2 →
  adSquare0 x0 x1 x2 v0 v1 v2
    - adSquare0 y0 y1 y2 v0 v1 v2
  ≡ ad0 x1 x2
      (ad1 (x0 - y0) (x2 - y2) v0 v2)
      (ad2 (x0 - y0) (x1 - y1) v0 v1)
    + ad0 (x1 - y1) (x2 - y2)
      (ad1 y0 y2 v0 v2)
      (ad2 y0 y1 v0 v1)
adSquareDifference0 x0 x1 x2 y0 y1 y2 v0 v1 v2 =
  ℚRing.solve-∀ x0 x1 x2 y0 y1 y2 v0 v1 v2

adSquareDifference1 : ∀ x0 x1 x2 y0 y1 y2 v0 v1 v2 →
  adSquare1 x0 x1 x2 v0 v1 v2
    - adSquare1 y0 y1 y2 v0 v1 v2
  ≡ ad1 x0 x2
      (ad0 (x1 - y1) (x2 - y2) v1 v2)
      (ad2 (x0 - y0) (x1 - y1) v0 v1)
    + ad1 (x0 - y0) (x2 - y2)
      (ad0 y1 y2 v1 v2)
      (ad2 y0 y1 v0 v1)
adSquareDifference1 x0 x1 x2 y0 y1 y2 v0 v1 v2 =
  ℚRing.solve-∀ x0 x1 x2 y0 y1 y2 v0 v1 v2

adSquareDifference2 : ∀ x0 x1 x2 y0 y1 y2 v0 v1 v2 →
  adSquare2 x0 x1 x2 v0 v1 v2
    - adSquare2 y0 y1 y2 v0 v1 v2
  ≡ ad2 x0 x1
      (ad0 (x1 - y1) (x2 - y2) v1 v2)
      (ad1 (x0 - y0) (x2 - y2) v0 v2)
    + ad2 (x0 - y0) (x1 - y1)
      (ad0 y1 y2 v1 v2)
      (ad1 y0 y2 v0 v2)
adSquareDifference2 x0 x1 x2 y0 y1 y2 v0 v1 v2 =
  ℚRing.solve-∀ x0 x1 x2 y0 y1 y2 v0 v1 v2

------------------------------------------------------------------------
-- Axis/ad-polynomial equality without dividing by the radius.
------------------------------------------------------------------------

axisCoefficientFromPolynomial : ℚ → ℚ → ℚ
axisCoefficientFromPolynomial c2 radius = 1ℚ - c2 * radius * radius

axisSkewFromPolynomial : ℚ → ℚ → ℚ
axisSkewFromPolynomial c1 radius = c1 * radius

adPolynomialAxis0Exact :
  ∀ c1 c2 radius n0 n1 n2 v0 v1 v2 →
  Axis.normSq3 n0 n1 n2 ≡ 1ℚ →
  principalLogAdPolynomial0 c1 c2
    (radius * n0) (radius * n1) (radius * n2) v0 v1 v2
  ≡ Axis.principalLogJacobian0
      (axisCoefficientFromPolynomial c2 radius)
      (axisSkewFromPolynomial c1 radius)
      n0 n1 n2 v0 v1 v2
adPolynomialAxis0Exact c1 c2 radius n0 n1 n2 v0 v1 v2 unit
  rewrite unit = ℚRing.solve-∀ c1 c2 radius n0 n1 n2 v0 v1 v2

adPolynomialAxis1Exact :
  ∀ c1 c2 radius n0 n1 n2 v0 v1 v2 →
  Axis.normSq3 n0 n1 n2 ≡ 1ℚ →
  principalLogAdPolynomial1 c1 c2
    (radius * n0) (radius * n1) (radius * n2) v0 v1 v2
  ≡ Axis.principalLogJacobian1
      (axisCoefficientFromPolynomial c2 radius)
      (axisSkewFromPolynomial c1 radius)
      n0 n1 n2 v0 v1 v2
adPolynomialAxis1Exact c1 c2 radius n0 n1 n2 v0 v1 v2 unit
  rewrite unit = ℚRing.solve-∀ c1 c2 radius n0 n1 n2 v0 v1 v2

adPolynomialAxis2Exact :
  ∀ c1 c2 radius n0 n1 n2 v0 v1 v2 →
  Axis.normSq3 n0 n1 n2 ≡ 1ℚ →
  principalLogAdPolynomial2 c1 c2
    (radius * n0) (radius * n1) (radius * n2) v0 v1 v2
  ≡ Axis.principalLogJacobian2
      (axisCoefficientFromPolynomial c2 radius)
      (axisSkewFromPolynomial c1 radius)
      n0 n1 n2 v0 v1 v2
adPolynomialAxis2Exact c1 c2 radius n0 n1 n2 v0 v1 v2 unit
  rewrite unit = ℚRing.solve-∀ c1 c2 radius n0 n1 n2 v0 v1 v2

cmp109SU2AdPolynomialTripleProductLevel : ProofLevel
cmp109SU2AdPolynomialTripleProductLevel = machineChecked

cmp109SU2AdPolynomialDifferenceLevel : ProofLevel
cmp109SU2AdPolynomialDifferenceLevel = machineChecked

cmp109SU2AxisFormEqualsAdPolynomialLevel : ProofLevel
cmp109SU2AxisFormEqualsAdPolynomialLevel = machineChecked
