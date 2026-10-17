module DASHI.Mathematics.Algebra.RationalAlbertFinite126SubgroupExact where

------------------------------------------------------------------------
-- FINITE 126-ELEMENT EXPLICIT ALBERT-AUTOMORPHISM SUBGROUP MAX-CUT
--
-- Extend the already-source-written order-7 Fano automorphism by the order-3
-- unsigned Fano automorphism
--
--   e1->e2, e2->e3, e3->e1, e4->e4, e5->e6, e6->e7, e7->e5.
--
-- The generators satisfy p3 p7 p3^-1 = p7^4, giving a 21-element
-- C7 semidirect C3 finite octonion-automorphism subgroup.  Applying those
-- automorphisms identically to all three Albert off-diagonal slots commutes with
-- the matrix-index S3 subgroup, so the executable finite action contains
-- 6*21 = 126 distinct maps.
--
-- The universal polynomial preservation laws below are source-written.  The
-- exact count 126 is retained as local exact-execution evidence rather than an
-- Agda-kernel group-cardinality theorem.  Nothing here identifies the finite
-- subgroup with full G2 or F4.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O
import DASHI.Mathematics.Algebra.RationalAlbertJordanExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanUnitExact as U
import DASHI.Mathematics.Algebra.RationalAlbertOctonionC7AutomorphismExact as C7
import DASHI.Mathematics.Algebra.RationalAlbertCyclicAutomorphismExact as C3Index
import DASHI.Mathematics.Algebra.RationalAlbertS3AutomorphismExact as S3Index
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q

c3Octonion : O.RationalOctonion → O.RationalOctonion
c3Octonion
  (O.oct
    (Q.quat a0 a1 a2 a3)
    (Q.quat a4 a5 a6 a7)) =
  O.oct
    (Q.quat a0 a3 a1 a2)
    (Q.quat a4 a7 a5 a6)

c3OctonionOrderThree : (value : O.RationalOctonion) →
  c3Octonion (c3Octonion (c3Octonion value)) ≡ value
c3OctonionOrderThree (O.oct (Q.quat _ _ _ _) (Q.quat _ _ _ _)) = refl

c3CommutesConjugation : (value : O.RationalOctonion) →
  c3Octonion (O.octonionConjugate value)
  ≡ O.octonionConjugate (c3Octonion value)
c3CommutesConjugation (O.oct (Q.quat _ _ _ _) (Q.quat _ _ _ _)) = refl

c3PreservesOctonionProduct : (left right : O.RationalOctonion) →
  c3Octonion (O._*o_ left right)
  ≡ O._*o_ (c3Octonion left) (c3Octonion right)
c3PreservesOctonionProduct
  (O.oct (Q.quat a0 a1 a2 a3) (Q.quat a4 a5 a6 a7))
  (O.oct (Q.quat b0 b1 b2 b3) (Q.quat b4 b5 b6 b7)) =
  O.octonionExt
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
  where
    vars : List ℚ
    vars =
      a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷
      b0 ∷ b1 ∷ b2 ∷ b3 ∷ b4 ∷ b5 ∷ b6 ∷ b7 ∷ []

c3Albert : A.RationalAlbert → A.RationalAlbert
c3Albert (A.albert a b c x1 x2 x3) =
  A.albert a b c (c3Octonion x1) (c3Octonion x2) (c3Octonion x3)

c3AlbertOrderThree : (value : A.RationalAlbert) →
  c3Albert (c3Albert (c3Albert value)) ≡ value
c3AlbertOrderThree (A.albert a b c x1 x2 x3) =
  U.albertExt refl refl refl
    (c3OctonionOrderThree x1)
    (c3OctonionOrderThree x2)
    (c3OctonionOrderThree x3)

c3AlbertPreservesJordan : (left right : A.RationalAlbert) →
  c3Albert (A.jordanProduct left right)
  ≡ A.jordanProduct (c3Albert left) (c3Albert right)
c3AlbertPreservesJordan
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

c3AlbertPreservesCubicNorm : (value : A.RationalAlbert) →
  A.cubicNorm (c3Albert value) ≡ A.cubicNorm value
c3AlbertPreservesCubicNorm
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

-- Semidirect relation at the octonion level: p3 p7 p3^-1 = p7^4.
c3InverseOctonion : O.RationalOctonion → O.RationalOctonion
c3InverseOctonion value = c3Octonion (c3Octonion value)

c7Fourth : O.RationalOctonion → O.RationalOctonion
c7Fourth value =
  C7.c7Octonion
    (C7.c7Octonion
      (C7.c7Octonion
        (C7.c7Octonion value)))

c21SemidirectRelation : (value : O.RationalOctonion) →
  c3Octonion (C7.c7Octonion (c3InverseOctonion value))
  ≡ c7Fourth value
c21SemidirectRelation (O.oct (Q.quat _ _ _ _) (Q.quat _ _ _ _)) = refl

-- Slotwise octonion automorphisms commute with the even matrix-index rotation.
c3AlbertCommutesIndexRotation : (value : A.RationalAlbert) →
  c3Albert (C3Index.rotateAlbert value)
  ≡ C3Index.rotateAlbert (c3Albert value)
c3AlbertCommutesIndexRotation (A.albert _ _ _ _ _ _) = refl

c7AlbertCommutesIndexRotation : (value : A.RationalAlbert) →
  C7.c7Albert (C3Index.rotateAlbert value)
  ≡ C3Index.rotateAlbert (C7.c7Albert value)
c7AlbertCommutesIndexRotation (A.albert _ _ _ _ _ _) = refl

-- Odd matrix-index permutations use conjugation; both p3 and p7 commute with
-- octonion conjugation, hence commute with the transposition generator too.
c3AlbertCommutesIndexSwap : (value : A.RationalAlbert) →
  c3Albert (S3Index.swap23Albert value)
  ≡ S3Index.swap23Albert (c3Albert value)
c3AlbertCommutesIndexSwap (A.albert a b c x1 x2 x3) =
  U.albertExt refl refl refl
    (c3CommutesConjugation x1)
    (c3CommutesConjugation x3)
    (c3CommutesConjugation x2)

c7AlbertCommutesIndexSwap : (value : A.RationalAlbert) →
  C7.c7Albert (S3Index.swap23Albert value)
  ≡ S3Index.swap23Albert (C7.c7Albert value)
c7AlbertCommutesIndexSwap (A.albert a b c x1 x2 x3) =
  U.albertExt refl refl refl
    (C7.c7CommutesConjugation x1)
    (C7.c7CommutesConjugation x3)
    (C7.c7CommutesConjugation x2)

record Finite126ExecutionReceipt : Set where
  constructor execution
  field
    octonionC7Order : Nat
    octonionC3Order : Nat
    generatedOctonionPermutationCount : Nat
    matrixIndexS3Count : Nat
    generatedAlbertPermutationCount : Nat
    exactLocalPermutationAuditPassed : Bool
    exactLocalAuditCountsAsAgdaKernelProof : Bool

open Finite126ExecutionReceipt public

canonicalExecutionReceipt : Finite126ExecutionReceipt
canonicalExecutionReceipt = execution 7 3 21 6 126 true false

record Finite126Boundary : Set where
  constructor boundary
  field
    c7OctonionSubgroupConstructed : Bool
    c3OctonionSubgroupConstructed : Bool
    c21SemidirectRelationSourceWritten : Bool
    c21OctonionSubgroupConstructed : Bool
    bothOctonionGeneratorsLiftToAlbertAutomorphisms : Bool
    matrixS3CommutesWithOctonionC21 : Bool
    generated126PaidAtExecutionGrade : Bool
    fullG2AutomorphismGroupConstructed : Bool
    fullF4AutomorphismGroupConstructed : Bool
    fullE6NormStabilizerConstructed : Bool

open Finite126Boundary public

canonicalBoundary : Finite126Boundary
canonicalBoundary =
  boundary true true true true true true true false false false
