module DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsCubicHomogeneityWitnessExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Rational.Solver using (module +-*-Solver)

open +-*-Solver using (solve; _:+_; _:-_; _:*_; con; _:=_)
open import DASHI.Core.Q using (ℚ; _+ℚ_; _-ℚ_; _*ℚ_; zeroℚ; oneℚ)
import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsCarrierExact as R
import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsLawObligationsExact as Laws
import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsBasicLawWitnessesExact as Basic

------------------------------------------------------------------------
-- CUBIC HOMOGENEITY ON THE LITERAL RATIONAL FIRST-TITS CARRIER
--
-- The proof is deliberately local.  It uses only the explicit M3(Q)^3
-- definitions and the repository's already-used rational polynomial solver.
-- No Albert/F4/E6 classification theorem is consumed.
--
-- The factorisation is:
--
--   det(qA) = q^3 det(A)
--   (qA)(rB) = qr(AB)
--   tr(qA) = q tr(A)
--
-- and therefore
--
--   N(qX) = q^3 N(X).
--
-- This file source-writes the proof term.  Without an exact-head Agda run the
-- receipt remains SOURCE-WRITTEN / KERNEL-UNVERIFIED.
------------------------------------------------------------------------

dotScale :
  (q r a0 a1 a2 b0 b1 b2 : ℚ) →
  ((q *ℚ a0) *ℚ (r *ℚ b0)) +ℚ
  ((q *ℚ a1) *ℚ (r *ℚ b1)) +ℚ
  ((q *ℚ a2) *ℚ (r *ℚ b2))
  ≡
  (q *ℚ r) *ℚ ((a0 *ℚ b0) +ℚ (a1 *ℚ b1) +ℚ (a2 *ℚ b2))
dotScale q r a0 a1 a2 b0 b1 b2 =
  solve 8
    (λ q' r' x0 x1 x2 y0 y1 y2 →
      ((q' :* x0) :* (r' :* y0)) :+
      ((q' :* x1) :* (r' :* y1)) :+
      ((q' :* x2) :* (r' :* y2))
      :=
      (q' :* r') :* ((x0 :* y0) :+ (x1 :* y1) :+ (x2 :* y2)))
    refl q r a0 a1 a2 b0 b1 b2

mulM-scale :
  (q r : ℚ) → (A B : R.QMatrix3) →
  R.mulM (R.scaleM q A) (R.scaleM r B)
  ≡ R.scaleM (q *ℚ r) (R.mulM A B)
mulM-scale q r A B =
  Basic.qmatrix3Ext
    (dotScale q r (R.m00 A) (R.m01 A) (R.m02 A) (R.m00 B) (R.m10 B) (R.m20 B))
    (dotScale q r (R.m00 A) (R.m01 A) (R.m02 A) (R.m01 B) (R.m11 B) (R.m21 B))
    (dotScale q r (R.m00 A) (R.m01 A) (R.m02 A) (R.m02 B) (R.m12 B) (R.m22 B))
    (dotScale q r (R.m10 A) (R.m11 A) (R.m12 A) (R.m00 B) (R.m10 B) (R.m20 B))
    (dotScale q r (R.m10 A) (R.m11 A) (R.m12 A) (R.m01 B) (R.m11 B) (R.m21 B))
    (dotScale q r (R.m10 A) (R.m11 A) (R.m12 A) (R.m02 B) (R.m12 B) (R.m22 B))
    (dotScale q r (R.m20 A) (R.m21 A) (R.m22 A) (R.m00 B) (R.m10 B) (R.m20 B))
    (dotScale q r (R.m20 A) (R.m21 A) (R.m22 A) (R.m01 B) (R.m11 B) (R.m21 B))
    (dotScale q r (R.m20 A) (R.m21 A) (R.m22 A) (R.m02 B) (R.m12 B) (R.m22 B))

traceM-scale :
  (q : ℚ) → (A : R.QMatrix3) →
  R.traceM (R.scaleM q A) ≡ q *ℚ R.traceM A
traceM-scale q A =
  solve 4
    (λ q' a b c →
      (q' :* a) :+ (q' :* b) :+ (q' :* c)
      := q' :* (a :+ b :+ c))
    refl q (R.m00 A) (R.m11 A) (R.m22 A)

tripleScale :
  (q a b c : ℚ) →
  ((q *ℚ a) *ℚ (q *ℚ b)) *ℚ (q *ℚ c)
  ≡ ((q *ℚ q) *ℚ q) *ℚ ((a *ℚ b) *ℚ c)
tripleScale q a b c =
  solve 4
    (λ q' x y z →
      ((q' :* x) :* (q' :* y)) :* (q' :* z)
      := ((q' :* q') :* q') :* ((x :* y) :* z))
    refl q a b c

detM-scale :
  (q : ℚ) → (A : R.QMatrix3) →
  R.detM (R.scaleM q A)
  ≡ ((q *ℚ q) *ℚ q) *ℚ R.detM A
detM-scale q (R.qmatrix3 a00 a01 a02 a10 a11 a12 a20 a21 a22)
  rewrite tripleScale q a00 a11 a22
        | tripleScale q a01 a12 a20
        | tripleScale q a02 a10 a21
        | tripleScale q a02 a11 a20
        | tripleScale q a01 a10 a22
        | tripleScale q a00 a12 a21 =
  solve 7
    (λ s p1 p2 p3 p4 p5 p6 →
      (s :* p1) :+ (s :* p2) :+ (s :* p3)
      :- (s :* p4) :- (s :* p5) :- (s :* p6)
      :=
      s :* (p1 :+ p2 :+ p3 :- p4 :- p5 :- p6))
    refl
    ((q *ℚ q) *ℚ q)
    ((a00 *ℚ a11) *ℚ a22)
    ((a01 *ℚ a12) *ℚ a20)
    ((a02 *ℚ a10) *ℚ a21)
    ((a02 *ℚ a11) *ℚ a20)
    ((a01 *ℚ a10) *ℚ a22)
    ((a00 *ℚ a12) *ℚ a21)

tripleTraceScale :
  (q : ℚ) → (A B C : R.QMatrix3) →
  R.traceM
    (R.mulM
      (R.mulM (R.scaleM q A) (R.scaleM q B))
      (R.scaleM q C))
  ≡
  ((q *ℚ q) *ℚ q) *ℚ R.traceM (R.mulM (R.mulM A B) C)
tripleTraceScale q A B C
  rewrite mulM-scale q q A B
        | mulM-scale (q *ℚ q) q (R.mulM A B) C
        | traceM-scale ((q *ℚ q) *ℚ q) (R.mulM (R.mulM A B) C) = refl

cubicHomogeneousWitness : Laws.CubicHomogeneous
cubicHomogeneousWitness q (R.rationalFirstTits27 A B C)
  rewrite detM-scale q A
        | detM-scale q B
        | detM-scale q C
        | tripleTraceScale q A B C =
  solve 5
    (λ s a b c t →
      (s :* a) :+ (s :* b) :+ (s :* c) :- (s :* t)
      := s :* (a :+ b :+ c :- t))
    refl
    ((q *ℚ q) *ℚ q)
    (R.detM A)
    (R.detM B)
    (R.detM C)
    (R.traceM (R.mulM (R.mulM A B) C))

record RationalFirstTitsCubicHomogeneityWitness : Set where
  constructor rational-first-tits-cubic-homogeneity-witness
  field
    cubicHomogeneous : Laws.CubicHomogeneous
open RationalFirstTitsCubicHomogeneityWitness public

canonicalCubicHomogeneityWitness : RationalFirstTitsCubicHomogeneityWitness
canonicalCubicHomogeneityWitness =
  rational-first-tits-cubic-homogeneity-witness cubicHomogeneousWitness

record CubicHomogeneityBoundary : Set where
  constructor cubic-homogeneity-boundary
  field
    determinantScalingTermSourceWritten : Bool
    matrixProductScalingTermSourceWritten : Bool
    traceScalingTermSourceWritten : Bool
    cubicHomogeneityTermSourceWritten : Bool
    externalAlbertClassificationUsed : Bool
    exactHeadAgdaKernelReceiptPresent : Bool
    boundary : String
open CubicHomogeneityBoundary public

canonicalBoundary : CubicHomogeneityBoundary
canonicalBoundary =
  cubic-homogeneity-boundary
    true true true true false false
    "Cubic homogeneity N(qX)=q^3 N(X) is source-written directly from the literal M3(Q)^3 first-Tits cubic using the repository rational polynomial solver. No Albert/F4/E6 classification theorem is used. The exact-head Agda kernel receipt remains separate and absent in this environment."
