module DASHI.Mathematics.Algebra.RationalAlbertCharacteristicExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Mathematics.Algebra.RationalAlbertJordanExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanUnitExact as U
import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q

------------------------------------------------------------------------
-- CUBIC CHARACTERISTIC IDENTITY
--
-- x^3 - tr(x) x^2 + S(x) x - N(x) 1 = 0,
-- S(x) = 1/2 (tr(x)^2 - tr(x^2)).
--
-- This ties the explicitly defined cubic norm to the Jordan product on the
-- same rational Albert carrier.  As in the Jordan-identity owner, all 27
-- coordinate equalities are rational polynomial identities after expansion.
------------------------------------------------------------------------

zeroAlbert : A.RationalAlbert
zeroAlbert = A.albert 0ℚ 0ℚ 0ℚ O.zeroO O.zeroO O.zeroO

scaleAlbert : ℚ → A.RationalAlbert → A.RationalAlbert
scaleAlbert q (A.albert a b c x1 x2 x3) =
  A.albert
    (q * a) (q * b) (q * c)
    (O._*o_ (A.scalarO q) x1)
    (O._*o_ (A.scalarO q) x2)
    (O._*o_ (A.scalarO q) x3)

addAlbert : A.RationalAlbert → A.RationalAlbert → A.RationalAlbert
addAlbert
  (A.albert a b c x1 x2 x3)
  (A.albert d e f y1 y2 y3) =
  A.albert
    (a + d) (b + e) (c + f)
    (O._+o_ x1 y1) (O._+o_ x2 y2) (O._+o_ x3 y3)

square : A.RationalAlbert → A.RationalAlbert
square x = A.jordanProduct x x

cube : A.RationalAlbert → A.RationalAlbert
cube x = A.jordanProduct (square x) x

secondCoefficient : A.RationalAlbert → ℚ
secondCoefficient x =
  A.qHalf *
    (A.albertTrace x * A.albertTrace x
     + -(A.albertTrace (square x)))

characteristicResidual : A.RationalAlbert → A.RationalAlbert
characteristicResidual x =
  addAlbert
    (addAlbert
      (cube x)
      (scaleAlbert (-(A.albertTrace x)) (square x)))
    (addAlbert
      (scaleAlbert (secondCoefficient x) x)
      (scaleAlbert (-(A.cubicNorm x)) A.albertUnit))

characteristicIdentity : (x : A.RationalAlbert) →
  characteristicResidual x ≡ zeroAlbert
characteristicIdentity
  (A.albert a b c
    (O.oct (Q.quat x10 x11 x12 x13) (Q.quat x14 x15 x16 x17))
    (O.oct (Q.quat x20 x21 x22 x23) (Q.quat x24 x25 x26 x27))
    (O.oct (Q.quat x30 x31 x32 x33) (Q.quat x34 x35 x36 x37))) =
  U.albertExt
    (solve vars) (solve vars) (solve vars)
    (O.octonionExt
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars)))
    (O.octonionExt
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars)))
    (O.octonionExt
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars)))
  where
    vars : List ℚ
    vars =
      a ∷ b ∷ c ∷
      x10 ∷ x11 ∷ x12 ∷ x13 ∷ x14 ∷ x15 ∷ x16 ∷ x17 ∷
      x20 ∷ x21 ∷ x22 ∷ x23 ∷ x24 ∷ x25 ∷ x26 ∷ x27 ∷
      x30 ∷ x31 ∷ x32 ∷ x33 ∷ x34 ∷ x35 ∷ x36 ∷ x37 ∷ []
