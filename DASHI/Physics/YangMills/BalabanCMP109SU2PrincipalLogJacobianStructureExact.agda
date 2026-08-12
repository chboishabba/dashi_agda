module DASHI.Physics.YangMills.BalabanCMP109SU2PrincipalLogJacobianStructureExact where

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
-- Isolate the exact three-dimensional algebra of the SU(2) principal-log
-- differential.  In an axis/plane decomposition the inverse-dexp operator has
-- the form
--
--   J v = a v + (1-a) <n,v> n + s (n x v),
--
-- where n is the logarithm axis, a = (theta/2) cot(theta/2) in the standard
-- SU(2) normalization, and the sign/value of s depends on left/right
-- trivialization.  The skew term does not contribute to <v,Jv>.  Hence
--
--   <v,Jv> = a |v|^2 + (1-a) <n,v>^2.
--
-- The identity is proved here over exact rationals for arbitrary a,s,n,v, so
-- it is independent of the analytic realization of a.  If 1-a is
-- nonnegative, the symmetric part is immediately bounded below by a I.  This
-- is the high-fan-out algebra consumed by both the equation-(0.11) Federbush
-- centre solve and equation-(0.12) principal-log derivative estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

dot3 : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
dot3 x0 x1 x2 y0 y1 y2 = x0 * y0 + x1 * y1 + x2 * y2

normSq3 : ℚ → ℚ → ℚ → ℚ
normSq3 x0 x1 x2 = x0 * x0 + x1 * x1 + x2 * x2

cross0 : ℚ → ℚ → ℚ → ℚ → ℚ
cross0 n1 n2 v1 v2 = n1 * v2 - n2 * v1

cross1 : ℚ → ℚ → ℚ → ℚ → ℚ
cross1 n0 n2 v0 v2 = n2 * v0 - n0 * v2

cross2 : ℚ → ℚ → ℚ → ℚ → ℚ
cross2 n0 n1 v0 v1 = n0 * v1 - n1 * v0

principalLogJacobian0 :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
principalLogJacobian0 a s n0 n1 n2 v0 v1 v2 =
  let d = dot3 n0 n1 n2 v0 v1 v2
  in a * v0 + (1ℚ - a) * d * n0 + s * cross0 n1 n2 v1 v2

principalLogJacobian1 :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
principalLogJacobian1 a s n0 n1 n2 v0 v1 v2 =
  let d = dot3 n0 n1 n2 v0 v1 v2
  in a * v1 + (1ℚ - a) * d * n1 + s * cross1 n0 n2 v0 v2

principalLogJacobian2 :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
principalLogJacobian2 a s n0 n1 n2 v0 v1 v2 =
  let d = dot3 n0 n1 n2 v0 v1 v2
  in a * v2 + (1ℚ - a) * d * n2 + s * cross2 n0 n1 v0 v1

principalLogJacobianQuadratic :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
principalLogJacobianQuadratic a s n0 n1 n2 v0 v1 v2 =
  v0 * principalLogJacobian0 a s n0 n1 n2 v0 v1 v2
  + v1 * principalLogJacobian1 a s n0 n1 n2 v0 v1 v2
  + v2 * principalLogJacobian2 a s n0 n1 n2 v0 v1 v2

crossTermQuadraticExact : ∀ n0 n1 n2 v0 v1 v2 →
  v0 * cross0 n1 n2 v1 v2
  + v1 * cross1 n0 n2 v0 v2
  + v2 * cross2 n0 n1 v0 v1
  ≡ 0ℚ
crossTermQuadraticExact n0 n1 n2 v0 v1 v2 =
  ℚRing.solve-∀ n0 n1 n2 v0 v1 v2

principalLogJacobianQuadraticExact :
  ∀ a s n0 n1 n2 v0 v1 v2 →
  principalLogJacobianQuadratic a s n0 n1 n2 v0 v1 v2
  ≡ a * normSq3 v0 v1 v2
    + (1ℚ - a)
      * (dot3 n0 n1 n2 v0 v1 v2
        * dot3 n0 n1 n2 v0 v1 v2)
principalLogJacobianQuadraticExact a s n0 n1 n2 v0 v1 v2 =
  ℚRing.solve-∀ a s n0 n1 n2 v0 v1 v2

principalLogSymmetricCoercive :
  ∀ a s n0 n1 n2 v0 v1 v2 →
  0ℚ ≤ 1ℚ - a →
  a * normSq3 v0 v1 v2
  ≤ principalLogJacobianQuadratic a s n0 n1 n2 v0 v1 v2
principalLogSymmetricCoercive
    a s n0 n1 n2 v0 v1 v2 identityGapNonnegative =
  let
    d = dot3 n0 n1 n2 v0 v1 v2
    tailNonnegative : 0ℚ ≤ (1ℚ - a) * (d * d)
    tailNonnegative =
      Norm.scaleNonnegative (1ℚ - a) identityGapNonnegative
        (FiniteL2.squareNonnegative d)

    raw :
      a * normSq3 v0 v1 v2
      ≤ a * normSq3 v0 v1 v2 + (1ℚ - a) * (d * d)
    raw =
      subst
        (λ left →
          left ≤ a * normSq3 v0 v1 v2 + (1ℚ - a) * (d * d))
        (sym (ℚP.+-identityʳ (a * normSq3 v0 v1 v2)))
        (ℚP.+-monoˡ-≤ (a * normSq3 v0 v1 v2) tailNonnegative)
  in
  subst
    (λ upper → a * normSq3 v0 v1 v2 ≤ upper)
    (sym (principalLogJacobianQuadraticExact
      a s n0 n1 n2 v0 v1 v2))
    raw

principalLogSkewOrientationIndependent :
  ∀ a s n0 n1 n2 v0 v1 v2 →
  principalLogJacobianQuadratic a s n0 n1 n2 v0 v1 v2
  ≡ principalLogJacobianQuadratic a (0ℚ - s) n0 n1 n2 v0 v1 v2
principalLogSkewOrientationIndependent a s n0 n1 n2 v0 v1 v2 =
  ℚRing.solve-∀ a s n0 n1 n2 v0 v1 v2

cmp109SU2PrincipalLogJacobianStructureLevel : ProofLevel
cmp109SU2PrincipalLogJacobianStructureLevel = machineChecked

cmp109SU2PrincipalLogSymmetricCoercivityLevel : ProofLevel
cmp109SU2PrincipalLogSymmetricCoercivityLevel = machineChecked
