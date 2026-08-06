module DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Give the exact noncommutative four-factor telescope consumed by every
-- Wilson plaquette atom.  For arbitrary rational quaternions A_i and B_i,
--
--   A0 A1 A2 A3 - B0 B1 B2 B3
--
-- is the sum of four terms, each containing exactly one factor difference:
--
--   (A0-B0) A1 A2 A3
-- + B0 (A1-B1) A2 A3
-- + B0 B1 (A2-B2) A3
-- + B0 B1 B2 (A3-B3).
--
-- The ordered products retain the repository's literal trailing unit factor,
-- so the theorem rewrites directly against orderedValueProduct and the named
-- sixteen-placement Wilson atom normal form.  No commutativity of quaternion
-- multiplication is used or assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q

infixl 6 _-q_

_-q_ : Q.RationalQuaternion → Q.RationalQuaternion → Q.RationalQuaternion
left -q right = left Q.+q Q.negQ right

orderedProduct4 :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion
orderedProduct4 factor0 factor1 factor2 factor3 =
  factor0 Q.*q
    (factor1 Q.*q
      (factor2 Q.*q
        (factor3 Q.*q Q.oneQ)))

fourFactorTelescope :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion
fourFactorTelescope a0 a1 a2 a3 b0 b1 b2 b3 =
  ((a0 -q b0) Q.*q
      (a1 Q.*q (a2 Q.*q (a3 Q.*q Q.oneQ))))
  Q.+q
  ((b0 Q.*q
      ((a1 -q b1) Q.*q
        (a2 Q.*q (a3 Q.*q Q.oneQ))))
  Q.+q
  ((b0 Q.*q
      (b1 Q.*q
        ((a2 -q b2) Q.*q (a3 Q.*q Q.oneQ))))
  Q.+q
   (b0 Q.*q
      (b1 Q.*q
        (b2 Q.*q ((a3 -q b3) Q.*q Q.oneQ))))))

fourFactorDifferenceTelescopeExact :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  orderedProduct4 a0 a1 a2 a3 -q orderedProduct4 b0 b1 b2 b3
  ≡ fourFactorTelescope a0 a1 a2 a3 b0 b1 b2 b3
fourFactorDifferenceTelescopeExact
    (Q.quat a00 a01 a02 a03)
    (Q.quat a10 a11 a12 a13)
    (Q.quat a20 a21 a22 a23)
    (Q.quat a30 a31 a32 a33)
    (Q.quat b00 b01 b02 b03)
    (Q.quat b10 b11 b12 b13)
    (Q.quat b20 b21 b22 b23)
    (Q.quat b30 b31 b32 b33) =
  Q.quaternionExt
    (ℚRing.solve-∀
      a00 a01 a02 a03 a10 a11 a12 a13
      a20 a21 a22 a23 a30 a31 a32 a33
      b00 b01 b02 b03 b10 b11 b12 b13
      b20 b21 b22 b23 b30 b31 b32 b33)
    (ℚRing.solve-∀
      a00 a01 a02 a03 a10 a11 a12 a13
      a20 a21 a22 a23 a30 a31 a32 a33
      b00 b01 b02 b03 b10 b11 b12 b13
      b20 b21 b22 b23 b30 b31 b32 b33)
    (ℚRing.solve-∀
      a00 a01 a02 a03 a10 a11 a12 a13
      a20 a21 a22 a23 a30 a31 a32 a33
      b00 b01 b02 b03 b10 b11 b12 b13
      b20 b21 b22 b23 b30 b31 b32 b33)
    (ℚRing.solve-∀
      a00 a01 a02 a03 a10 a11 a12 a13
      a20 a21 a22 a23 a30 a31 a32 a33
      b00 b01 b02 b03 b10 b11 b12 b13
      b20 b21 b22 b23 b30 b31 b32 b33)

wilsonScalar : Q.RationalQuaternion → ℚ
wilsonScalar value = - Q.q0 value

wilsonScalarDifference :
  Q.RationalQuaternion → Q.RationalQuaternion → ℚ
wilsonScalarDifference left right =
  wilsonScalar left - wilsonScalar right

wilsonScalarDifferenceIsNegativeScalarPart :
  ∀ left right →
  wilsonScalarDifference left right ≡ - Q.q0 (left -q right)
wilsonScalarDifferenceIsNegativeScalarPart
    (Q.quat a0 a1 a2 a3)
    (Q.quat b0 b1 b2 b3) =
  ℚRing.solve-∀ a0 b0

wilsonScalarDifferenceTelescopeExact :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  wilsonScalarDifference
    (orderedProduct4 a0 a1 a2 a3)
    (orderedProduct4 b0 b1 b2 b3)
  ≡ wilsonScalar
      (fourFactorTelescope a0 a1 a2 a3 b0 b1 b2 b3)
wilsonScalarDifferenceTelescopeExact
    a0 a1 a2 a3 b0 b1 b2 b3 =
  let
    leftProduct = orderedProduct4 a0 a1 a2 a3
    rightProduct = orderedProduct4 b0 b1 b2 b3

    quaternionExact :
      leftProduct -q rightProduct
      ≡ fourFactorTelescope a0 a1 a2 a3 b0 b1 b2 b3
    quaternionExact =
      fourFactorDifferenceTelescopeExact
        a0 a1 a2 a3 b0 b1 b2 b3
  in
  trans
    (wilsonScalarDifferenceIsNegativeScalarPart
      leftProduct rightProduct)
    (cong (λ selected → - Q.q0 selected) quaternionExact)

quaternionFourFactorTelescopeLevel : ProofLevel
quaternionFourFactorTelescopeLevel = machineChecked

wilsonScalarTelescopeLevel : ProofLevel
wilsonScalarTelescopeLevel = machineChecked
