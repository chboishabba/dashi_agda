module DASHI.Mathematics.Topology.QuaternionHopfRadiusExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Heinz Hopf,
-- "Über die Abbildungen der dreidimensionalen Sphäre auf die Kugelfläche".
-- DOI: 10.1007/BF01457962.
--
-- A. A. Belavin, A. M. Polyakov, A. S. Schwartz and Yu. S. Tyupkin,
-- "Pseudoparticle Solutions of the Yang--Mills Equations",
-- Physics Letters B 59 (1975), 85--87.
-- DOI: 10.1016/0370-2693(75)90163-X.
--
-- John C. Baez,
-- "The Octonions".
-- DOI: 10.1090/S0273-0979-01-00934-X.
--
-- DASHI CONTRIBUTION
--
-- Implement the polynomial core of the quaternionic Hopf map on the exact
-- rational quaternion carrier already used by the Yang--Mills development:
--
--   H(a,b) = (2 a conjugate(b), |a|^2 - |b|^2).
--
-- The checked identity is
--
--   |2 a conjugate(b)|^2 + (|a|^2-|b|^2)^2
--     = (|a|^2+|b|^2)^2.
--
-- Thus a rational point satisfying |a|^2+|b|^2=1 maps to a rational point on
-- the target unit quadric.  This is the exact algebraic radius identity only:
-- smooth sphere structure, local triviality, fibres, characteristic classes,
-- instanton connections and Chern-number integrality remain separate results.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as CD

QuaternionCarrier : Set
QuaternionCarrier = Q.RationalQuaternion

scalarQuaternion : ℚ → Q.RationalQuaternion
scalarQuaternion value = Q.quat value 0ℚ 0ℚ 0ℚ

scaleQuaternion : ℚ → Q.RationalQuaternion → Q.RationalQuaternion
scaleQuaternion scale (Q.quat a0 a1 a2 a3) =
  Q.quat (scale * a0) (scale * a1) (scale * a2) (scale * a3)

scaleQuaternionNormSq : ∀ scale value →
  CD.quaternionNormSq (scaleQuaternion scale value)
  ≡ (scale * scale) * CD.quaternionNormSq value
scaleQuaternionNormSq scale (Q.quat a0 a1 a2 a3) =
  solve (scale ∷ a0 ∷ a1 ∷ a2 ∷ a3 ∷ [])

quaternionTimesConjugate : ∀ value →
  Q._*q_ value (CD.quaternionConjugate value)
  ≡ scalarQuaternion (CD.quaternionNormSq value)
quaternionTimesConjugate (Q.quat a0 a1 a2 a3) =
  Q.quaternionExt
    (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []))
    (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []))
    (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []))
    (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []))

conjugateTimesQuaternion : ∀ value →
  Q._*q_ (CD.quaternionConjugate value) value
  ≡ scalarQuaternion (CD.quaternionNormSq value)
conjugateTimesQuaternion (Q.quat a0 a1 a2 a3) =
  Q.quaternionExt
    (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []))
    (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []))
    (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []))
    (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []))

hopfQuaternion : Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion
hopfQuaternion a b =
  scaleQuaternion (+ 2 / 1)
    (Q._*q_ a (CD.quaternionConjugate b))

hopfScalar : Q.RationalQuaternion → Q.RationalQuaternion → ℚ
hopfScalar a b =
  CD.quaternionNormSq a - CD.quaternionNormSq b

hopfTargetNormSq : Q.RationalQuaternion → Q.RationalQuaternion → ℚ
hopfTargetNormSq a b =
  CD.quaternionNormSq (hopfQuaternion a b)
  + hopfScalar a b * hopfScalar a b

quaternionHopfRadiusIdentity : ∀ a b →
  hopfTargetNormSq a b
  ≡ (CD.quaternionNormSq a + CD.quaternionNormSq b)
    * (CD.quaternionNormSq a + CD.quaternionNormSq b)
quaternionHopfRadiusIdentity
    (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3) =
  solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ [])

unitPairMapsToTargetUnitQuadric : ∀ a b →
  CD.quaternionNormSq a + CD.quaternionNormSq b ≡ 1ℚ →
  hopfTargetNormSq a b ≡ 1ℚ
unitPairMapsToTargetUnitQuadric a b unitPair
  rewrite quaternionHopfRadiusIdentity a b | unitPair =
  solve []

hopfAtOneZero :
  hopfQuaternion Q.oneQ Q.zeroQ ≡ Q.zeroQ
hopfAtOneZero =
  Q.quaternionExt (solve []) (solve []) (solve []) (solve [])

hopfScalarAtOneZero :
  hopfScalar Q.oneQ Q.zeroQ ≡ 1ℚ
hopfScalarAtOneZero = solve []

hopfTargetNormAtOneZero :
  hopfTargetNormSq Q.oneQ Q.zeroQ ≡ 1ℚ
hopfTargetNormAtOneZero = solve []
