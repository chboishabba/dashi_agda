module DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- John H. Conway and Derek A. Smith,
-- "On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry",
-- A K Peters, 2003. DOI: 10.1201/9781439864180.
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
-- Supply the exact ordered rational norm algebra needed by the physical Wilson
-- and gauge defect estimates, without introducing square roots:
--
--   N(q r) = N(q) N(r),
--   N(conj q) = N(q),
--   q0(q)^2 <= N(q),
--   N(q+r) <= 2 (N(q)+N(r)),
--   N(q0+q1+q2+q3) <= 4 sum_i N(q_i).
--
-- All statements are over exact rationals.  The two- and four-term estimates
-- are proved from the nonnegative square `(a-b)^2`, so no analytic norm axiom,
-- square root, or imported Cauchy--Schwarz receipt is used.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_; _/_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q

normSq : Q.RationalQuaternion → ℚ
normSq (Q.quat q0 q1 q2 q3) =
  q0 * q0 + q1 * q1 + q2 * q2 + q3 * q3

conjugate : Q.RationalQuaternion → Q.RationalQuaternion
conjugate (Q.quat q0 q1 q2 q3) =
  Q.quat q0 (- q1) (- q2) (- q3)

normSqNonnegative : ∀ value → 0ℚ ≤ normSq value
normSqNonnegative (Q.quat q0 q1 q2 q3) =
  FiniteL2.addNonnegative
    (FiniteL2.addNonnegative
      (FiniteL2.addNonnegative
        (FiniteL2.squareNonnegative q0)
        (FiniteL2.squareNonnegative q1))
      (FiniteL2.squareNonnegative q2))
    (FiniteL2.squareNonnegative q3)

normSqMultiplyExact : ∀ left right →
  normSq (left Q.*q right) ≡ normSq left * normSq right
normSqMultiplyExact
    (Q.quat a0 a1 a2 a3)
    (Q.quat b0 b1 b2 b3) =
  ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3

normSqConjugateExact : ∀ value →
  normSq (conjugate value) ≡ normSq value
normSqConjugateExact (Q.quat q0 q1 q2 q3) =
  ℚRing.solve-∀ q0 q1 q2 q3

scalarPartSquareBelowNormSq : ∀ value →
  Q.q0 value * Q.q0 value ≤ normSq value
scalarPartSquareBelowNormSq (Q.quat q0 q1 q2 q3) =
  let
    tailNonnegative :
      0ℚ ≤ q1 * q1 + q2 * q2 + q3 * q3
    tailNonnegative =
      FiniteL2.addNonnegative
        (FiniteL2.addNonnegative
          (FiniteL2.squareNonnegative q1)
          (FiniteL2.squareNonnegative q2))
        (FiniteL2.squareNonnegative q3)
  in
  subst
    (λ lower → lower ≤ q0 * q0 + q1 * q1 + q2 * q2 + q3 * q3)
    (ℚP.+-identityʳ (q0 * q0))
    (ℚP.+-monoʳ-≤ (q0 * q0) tailNonnegative)

nonnegativeDifferenceImpliesBelow : ∀ {lower upper} →
  0ℚ ≤ upper - lower → lower ≤ upper
nonnegativeDifferenceImpliesBelow {lower} {upper} differenceNonnegative =
  let
    translated : lower + 0ℚ ≤ lower + (upper - lower)
    translated = ℚP.+-monoˡ-≤ lower differenceNonnegative
  in
  subst
    (λ left → left ≤ upper)
    (ℚP.+-identityʳ lower)
    (subst
      (λ right → lower + 0ℚ ≤ right)
      (ℚRing.solve-∀ lower upper)
      translated)

scalarTwoTermSquareBound : ∀ left right →
  (left + right) * (left + right)
  ≤ (+ 2 / 1) * (left * left + right * right)
scalarTwoTermSquareBound left right =
  nonnegativeDifferenceImpliesBelow
    (subst
      (λ selected → 0ℚ ≤ selected)
      (ℚRing.solve-∀ left right)
      (FiniteL2.squareNonnegative (left - right)))

normSqAddBound : ∀ left right →
  normSq (left Q.+q right)
  ≤ (+ 2 / 1) * (normSq left + normSq right)
normSqAddBound
    (Q.quat a0 a1 a2 a3)
    (Q.quat b0 b1 b2 b3) =
  let
    components :
      (a0 + b0) * (a0 + b0)
        + (a1 + b1) * (a1 + b1)
        + (a2 + b2) * (a2 + b2)
        + (a3 + b3) * (a3 + b3)
      ≤ (+ 2 / 1) * (a0 * a0 + b0 * b0)
        + (+ 2 / 1) * (a1 * a1 + b1 * b1)
        + (+ 2 / 1) * (a2 * a2 + b2 * b2)
        + (+ 2 / 1) * (a3 * a3 + b3 * b3)
    components =
      ℚP.+-mono-≤
        (ℚP.+-mono-≤
          (ℚP.+-mono-≤
            (scalarTwoTermSquareBound a0 b0)
            (scalarTwoTermSquareBound a1 b1))
          (scalarTwoTermSquareBound a2 b2))
        (scalarTwoTermSquareBound a3 b3)
  in
  subst
    (λ upper →
      normSq
        (Q.quat (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3))
      ≤ upper)
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3)
    components

scaleNonnegative : ∀ scale {left right} →
  0ℚ ≤ scale → left ≤ right → scale * left ≤ scale * right
scaleNonnegative scale scaleNonnegativeProof leftBelowRight =
  let
    instance
      scaleNN : NonNegative scale
      scaleNN = ℚ.nonNegative scaleNonnegativeProof
  in
  ℚP.*-monoˡ-≤-nonNeg scale leftBelowRight

normSqSum4Bound : ∀ first second third fourth →
  normSq (first Q.+q (second Q.+q (third Q.+q fourth)))
  ≤ (+ 4 / 1)
      * (normSq first + normSq second
        + normSq third + normSq fourth)
normSqSum4Bound first second third fourth =
  let
    leftPair = first Q.+q second
    rightPair = third Q.+q fourth

    reassociate :
      first Q.+q (second Q.+q (third Q.+q fourth))
      ≡ leftPair Q.+q rightPair
    reassociate =
      sym (Q.quaternionAddAssociative first second (third Q.+q fourth))

    outer :
      normSq (leftPair Q.+q rightPair)
      ≤ (+ 2 / 1) * (normSq leftPair + normSq rightPair)
    outer = normSqAddBound leftPair rightPair

    innerSum :
      normSq leftPair + normSq rightPair
      ≤ (+ 2 / 1) * (normSq first + normSq second)
        + (+ 2 / 1) * (normSq third + normSq fourth)
    innerSum =
      ℚP.+-mono-≤
        (normSqAddBound first second)
        (normSqAddBound third fourth)

    scaledInner :
      (+ 2 / 1) * (normSq leftPair + normSq rightPair)
      ≤ (+ 2 / 1)
          * ((+ 2 / 1) * (normSq first + normSq second)
            + (+ 2 / 1) * (normSq third + normSq fourth))
    scaledInner =
      scaleNonnegative (+ 2 / 1)
        (ℚP.nonNegative⁻¹ (+ 2 / 1)) innerSum

    combined :
      normSq (leftPair Q.+q rightPair)
      ≤ (+ 2 / 1)
          * ((+ 2 / 1) * (normSq first + normSq second)
            + (+ 2 / 1) * (normSq third + normSq fourth))
    combined = ℚP.≤-trans outer scaledInner
  in
  subst
    (λ lower →
      normSq lower
      ≤ (+ 4 / 1)
          * (normSq first + normSq second
            + normSq third + normSq fourth))
    (sym reassociate)
    (subst
      (λ upper →
        normSq (leftPair Q.+q rightPair) ≤ upper)
      (ℚRing.solve-∀
        (normSq first) (normSq second)
        (normSq third) (normSq fourth))
      combined)

rationalQuaternionNormMultiplicativeLevel : ProofLevel
rationalQuaternionNormMultiplicativeLevel = machineChecked

rationalQuaternionScalarPartBoundLevel : ProofLevel
rationalQuaternionScalarPartBoundLevel = machineChecked

rationalQuaternionFiniteTriangleSquaredLevel : ProofLevel
rationalQuaternionFiniteTriangleSquaredLevel = machineChecked
