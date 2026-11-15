module DASHI.Mathematics.Algebra.RationalAlbertCyclicAutomorphismExact where

------------------------------------------------------------------------
-- A CONCRETE C3 SUBGROUP OF THE RATIONAL ALBERT AUTOMORPHISM / NORM-STABILIZER
--
-- Cyclically permuting the three Hermitian matrix indices sends
--
--   (a1,a2,a3 ; x1,x2,x3) -> (a2,a3,a1 ; x2,x3,x1).
--
-- The operation has order three, fixes the distinguished unit, preserves the
-- Jordan product and preserves the cubic norm.  This constructs a genuine
-- nontrivial exceptional-structure subgroup witness without promoting it to the
-- full F4 automorphism group or full E6 cubic-norm stabilizer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Mathematics.Algebra.RationalAlbertJordanExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanUnitExact as U
import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q

rotateAlbert : A.RationalAlbert → A.RationalAlbert
rotateAlbert (A.albert a b c x1 x2 x3) =
  A.albert b c a x2 x3 x1

rotateAlbertTwice : A.RationalAlbert → A.RationalAlbert
rotateAlbertTwice value = rotateAlbert (rotateAlbert value)

rotateAlbertThrice : (value : A.RationalAlbert) →
  rotateAlbert (rotateAlbert (rotateAlbert value)) ≡ value
rotateAlbertThrice (A.albert _ _ _ _ _ _) = refl

rotateAlbertUnit : rotateAlbert A.albertUnit ≡ A.albertUnit
rotateAlbertUnit = refl

rotatePreservesJordan : (left right : A.RationalAlbert) →
  rotateAlbert (A.jordanProduct left right)
  ≡
  A.jordanProduct (rotateAlbert left) (rotateAlbert right)
rotatePreservesJordan
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

rotatePreservesCubicNorm : (value : A.RationalAlbert) →
  A.cubicNorm (rotateAlbert value) ≡ A.cubicNorm value
rotatePreservesCubicNorm
  (A.albert a b c
    (O.oct (Q.quat x10 x11 x12 x13) (Q.quat x14 x15 x16 x17))
    (O.oct (Q.quat x20 x21 x22 x23) (Q.quat x24 x25 x26 x27))
    (O.oct (Q.quat x30 x31 x32 x33) (Q.quat x34 x35 x36 x37))) =
  solve vars
  where
    vars : List ℚ
    vars =
      a ∷ b ∷ c ∷
      x10 ∷ x11 ∷ x12 ∷ x13 ∷ x14 ∷ x15 ∷ x16 ∷ x17 ∷
      x20 ∷ x21 ∷ x22 ∷ x23 ∷ x24 ∷ x25 ∷ x26 ∷ x27 ∷
      x30 ∷ x31 ∷ x32 ∷ x33 ∷ x34 ∷ x35 ∷ x36 ∷ x37 ∷ []

record CyclicAlbertExceptionalSubgroupBoundary : Set where
  constructor boundary
  field
    orderThreeMapConstructed : Bool
    orderThreeLawSourceWritten : Bool
    fixesAlbertUnitSourceWritten : Bool
    preservesJordanProductSourceWritten : Bool
    preservesCubicNormSourceWritten : Bool
    givesConcreteAlbertAutomorphismSubgroup : Bool
    givesConcreteCubicNormStabilizerSubgroup : Bool
    fullF4AutomorphismGroupConstructedHere : Bool
    fullE6NormStabilizerConstructedHere : Bool

open CyclicAlbertExceptionalSubgroupBoundary public

canonicalCyclicAlbertExceptionalSubgroupBoundary :
  CyclicAlbertExceptionalSubgroupBoundary
canonicalCyclicAlbertExceptionalSubgroupBoundary =
  boundary true true true true true true true false false

cyclicAlbertAutomorphismSourceWritten : Bool
cyclicAlbertAutomorphismSourceWritten = true
