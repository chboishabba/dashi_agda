module DASHI.Mathematics.Algebra.RationalAlbertJordanIdentityExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Mathematics.Algebra.RationalAlbertJordanExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanUnitExact as U
import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q

------------------------------------------------------------------------
-- UNIVERSAL JORDAN IDENTITY FOR THE EXPLICIT RATIONAL ALBERT PRODUCT
--
--   ((x o x) o y) o x = (x o x) o (y o x)
--
-- Since every operation in the repo-native rational octonion implementation is
-- an explicit rational polynomial, both sides can be expanded coordinatewise.
-- This source proof asks the rational ring solver to close all 27 independent
-- Hermitian coordinates for two arbitrary 27-coordinate inputs.
--
-- SOURCE-WRITTEN: the current execution environment cannot run Agda, so this
-- theorem is not promoted to kernel-verified status until an exact-head receipt
-- exists.
------------------------------------------------------------------------

jordanIdentity :
  (x y : A.RationalAlbert) →
  A.jordanProduct (A.jordanProduct (A.jordanProduct x x) y) x
  ≡
  A.jordanProduct (A.jordanProduct x x) (A.jordanProduct y x)
jordanIdentity
  (A.albert a b c
    (O.oct (Q.quat x10 x11 x12 x13) (Q.quat x14 x15 x16 x17))
    (O.oct (Q.quat x20 x21 x22 x23) (Q.quat x24 x25 x26 x27))
    (O.oct (Q.quat x30 x31 x32 x33) (Q.quat x34 x35 x36 x37)))
  (A.albert d e f
    (O.oct (Q.quat y10 y11 y12 y13) (Q.quat y14 y15 y16 y17))
    (O.oct (Q.quat y20 y21 y22 y23) (Q.quat y24 y25 y26 y27))
    (O.oct (Q.quat y30 y31 y32 y33) (Q.quat y34 y35 y36 y37))) =
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
      x30 ∷ x31 ∷ x32 ∷ x33 ∷ x34 ∷ x35 ∷ x36 ∷ x37 ∷
      d ∷ e ∷ f ∷
      y10 ∷ y11 ∷ y12 ∷ y13 ∷ y14 ∷ y15 ∷ y16 ∷ y17 ∷
      y20 ∷ y21 ∷ y22 ∷ y23 ∷ y24 ∷ y25 ∷ y26 ∷ y27 ∷
      y30 ∷ y31 ∷ y32 ∷ y33 ∷ y34 ∷ y35 ∷ y36 ∷ y37 ∷ []
