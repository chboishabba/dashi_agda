module DASHI.Mathematics.Algebra.RationalAlbertCharacteristicIdentityExact where

------------------------------------------------------------------------
-- CUBIC CHARACTERISTIC IDENTITY FOR THE REPO-NATIVE RATIONAL ALBERT ALGEBRA
--
--   X^3 - tr(X) X^2 + sigma(X) X - N(X) 1 = 0
--
-- where sigma(X) = (tr(X)^2 - tr(X^2))/2 and powers use the Jordan product.
-- The proof expands one arbitrary 27-coordinate Albert element and closes every
-- rational coordinate with the exact ring solver.  It is SOURCE-WRITTEN until
-- an exact-head Agda kernel receipt exists.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Mathematics.Algebra.RationalAlbertJordanExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanUnitExact as U
import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q

addAlbert : A.RationalAlbert → A.RationalAlbert → A.RationalAlbert
addAlbert left right =
  A.albert
    (A.diag1 left + A.diag1 right)
    (A.diag2 left + A.diag2 right)
    (A.diag3 left + A.diag3 right)
    (O._+o_ (A.x1 left) (A.x1 right))
    (O._+o_ (A.x2 left) (A.x2 right))
    (O._+o_ (A.x3 left) (A.x3 right))

scaleAlbert : ℚ → A.RationalAlbert → A.RationalAlbert
scaleAlbert q value =
  A.albert
    (q * A.diag1 value)
    (q * A.diag2 value)
    (q * A.diag3 value)
    (O._*o_ (A.scalarO q) (A.x1 value))
    (O._*o_ (A.scalarO q) (A.x2 value))
    (O._*o_ (A.scalarO q) (A.x3 value))

zeroAlbert : A.RationalAlbert
zeroAlbert = A.albert 0ℚ 0ℚ 0ℚ O.zeroO O.zeroO O.zeroO

squareAlbert : A.RationalAlbert → A.RationalAlbert
squareAlbert value = A.jordanProduct value value

cubeAlbert : A.RationalAlbert → A.RationalAlbert
cubeAlbert value = A.jordanProduct (squareAlbert value) value

sigma2 : A.RationalAlbert → ℚ
sigma2 value =
  A.qHalf *
    ((A.albertTrace value * A.albertTrace value)
      - A.albertTrace (squareAlbert value))

characteristicResidual : A.RationalAlbert → A.RationalAlbert
characteristicResidual value =
  addAlbert
    (cubeAlbert value)
    (addAlbert
      (scaleAlbert (- A.albertTrace value) (squareAlbert value))
      (addAlbert
        (scaleAlbert (sigma2 value) value)
        (scaleAlbert (- A.cubicNorm value) A.albertUnit)))

characteristicIdentity : (value : A.RationalAlbert) →
  characteristicResidual value ≡ zeroAlbert
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

characteristicIdentitySourceWritten : Bool
characteristicIdentitySourceWritten = true
