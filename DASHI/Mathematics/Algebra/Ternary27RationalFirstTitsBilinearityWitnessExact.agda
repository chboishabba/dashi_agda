module DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsBilinearityWitnessExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Data.Rational.Solver using (module +-*-Solver)

open +-*-Solver using (solve; _:+_; _:-_; _:*_; con; _:=_)
open import DASHI.Core.Q using (ℚ; _+ℚ_; _-ℚ_; _*ℚ_; zeroℚ; oneℚ)
import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsCarrierExact as R
import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsLawObligationsExact as Laws
import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsBasicLawWitnessesExact as Basic

------------------------------------------------------------------------
-- BILINEARITY OF THE LITERAL M3(Q)^3 FIRST-TITS PRODUCT
--
-- The proof is factorised through literal matrix linearity.  No Albert/F4/E6
-- classification theorem is used.  The nonlinear-looking `crossM` term is
-- handled explicitly after proving linearity of trace and `bulletM`.
--
-- SOURCE-WRITTEN / KERNEL-UNVERIFIED until an exact-head Agda run exists.
------------------------------------------------------------------------

scaleM-add : (q : ℚ) → (A B : R.QMatrix3) →
  R.scaleM q (R.addM A B) ≡ R.addM (R.scaleM q A) (R.scaleM q B)
scaleM-add q A B =
  Basic.qmatrix3Ext
    (solve 3 (λ q' a b → q' :* (a :+ b) := (q' :* a) :+ (q' :* b)) refl q (R.m00 A) (R.m00 B))
    (solve 3 (λ q' a b → q' :* (a :+ b) := (q' :* a) :+ (q' :* b)) refl q (R.m01 A) (R.m01 B))
    (solve 3 (λ q' a b → q' :* (a :+ b) := (q' :* a) :+ (q' :* b)) refl q (R.m02 A) (R.m02 B))
    (solve 3 (λ q' a b → q' :* (a :+ b) := (q' :* a) :+ (q' :* b)) refl q (R.m10 A) (R.m10 B))
    (solve 3 (λ q' a b → q' :* (a :+ b) := (q' :* a) :+ (q' :* b)) refl q (R.m11 A) (R.m11 B))
    (solve 3 (λ q' a b → q' :* (a :+ b) := (q' :* a) :+ (q' :* b)) refl q (R.m12 A) (R.m12 B))
    (solve 3 (λ q' a b → q' :* (a :+ b) := (q' :* a) :+ (q' :* b)) refl q (R.m20 A) (R.m20 B))
    (solve 3 (λ q' a b → q' :* (a :+ b) := (q' :* a) :+ (q' :* b)) refl q (R.m21 A) (R.m21 B))
    (solve 3 (λ q' a b → q' :* (a :+ b) := (q' :* a) :+ (q' :* b)) refl q (R.m22 A) (R.m22 B))

scaleM-add-scalar : (q r : ℚ) → (A : R.QMatrix3) →
  R.scaleM (q +ℚ r) A ≡ R.addM (R.scaleM q A) (R.scaleM r A)
scaleM-add-scalar q r A =
  Basic.qmatrix3Ext
    (solve 3 (λ q' r' a → (q' :+ r') :* a := (q' :* a) :+ (r' :* a)) refl q r (R.m00 A))
    (solve 3 (λ q' r' a → (q' :+ r') :* a := (q' :* a) :+ (r' :* a)) refl q r (R.m01 A))
    (solve 3 (λ q' r' a → (q' :+ r') :* a := (q' :* a) :+ (r' :* a)) refl q r (R.m02 A))
    (solve 3 (λ q' r' a → (q' :+ r') :* a := (q' :* a) :+ (r' :* a)) refl q r (R.m10 A))
    (solve 3 (λ q' r' a → (q' :+ r') :* a := (q' :* a) :+ (r' :* a)) refl q r (R.m11 A))
    (solve 3 (λ q' r' a → (q' :+ r') :* a := (q' :* a) :+ (r' :* a)) refl q r (R.m12 A))
    (solve 3 (λ q' r' a → (q' :+ r') :* a := (q' :* a) :+ (r' :* a)) refl q r (R.m20 A))
    (solve 3 (λ q' r' a → (q' :+ r') :* a := (q' :* a) :+ (r' :* a)) refl q r (R.m21 A))
    (solve 3 (λ q' r' a → (q' :+ r') :* a := (q' :* a) :+ (r' :* a)) refl q r (R.m22 A))

scaleM-compose : (q r : ℚ) → (A : R.QMatrix3) →
  R.scaleM q (R.scaleM r A) ≡ R.scaleM (q *ℚ r) A
scaleM-compose q r A =
  Basic.qmatrix3Ext
    (solve 3 (λ q' r' a → q' :* (r' :* a) := (q' :* r') :* a) refl q r (R.m00 A))
    (solve 3 (λ q' r' a → q' :* (r' :* a) := (q' :* r') :* a) refl q r (R.m01 A))
    (solve 3 (λ q' r' a → q' :* (r' :* a) := (q' :* r') :* a) refl q r (R.m02 A))
    (solve 3 (λ q' r' a → q' :* (r' :* a) := (q' :* r') :* a) refl q r (R.m10 A))
    (solve 3 (λ q' r' a → q' :* (r' :* a) := (q' :* r') :* a) refl q r (R.m11 A))
    (solve 3 (λ q' r' a → q' :* (r' :* a) := (q' :* r') :* a) refl q r (R.m12 A))
    (solve 3 (λ q' r' a → q' :* (r' :* a) := (q' :* r') :* a) refl q r (R.m20 A))
    (solve 3 (λ q' r' a → q' :* (r' :* a) := (q' :* r') :* a) refl q r (R.m21 A))
    (solve 3 (λ q' r' a → q' :* (r' :* a) := (q' :* r') :* a) refl q r (R.m22 A))

dotAddLeft : (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℚ) →
  ((a0 +ℚ b0) *ℚ c0) +ℚ ((a1 +ℚ b1) *ℚ c1) +ℚ ((a2 +ℚ b2) *ℚ c2)
  ≡
  ((a0 *ℚ c0) +ℚ (a1 *ℚ c1) +ℚ (a2 *ℚ c2)) +ℚ
  ((b0 *ℚ c0) +ℚ (b1 *ℚ c1) +ℚ (b2 *ℚ c2))
dotAddLeft a0 a1 a2 b0 b1 b2 c0 c1 c2 =
  solve 9
    (λ a0' a1' a2' b0' b1' b2' c0' c1' c2' →
      ((a0' :+ b0') :* c0') :+ ((a1' :+ b1') :* c1') :+ ((a2' :+ b2') :* c2')
      :=
      ((a0' :* c0') :+ (a1' :* c1') :+ (a2' :* c2')) :+
      ((b0' :* c0') :+ (b1' :* c1') :+ (b2' :* c2')))
    refl a0 a1 a2 b0 b1 b2 c0 c1 c2

dotAddRight : (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℚ) →
  (a0 *ℚ (b0 +ℚ c0)) +ℚ (a1 *ℚ (b1 +ℚ c1)) +ℚ (a2 *ℚ (b2 +ℚ c2))
  ≡
  ((a0 *ℚ b0) +ℚ (a1 *ℚ b1) +ℚ (a2 *ℚ b2)) +ℚ
  ((a0 *ℚ c0) +ℚ (a1 *ℚ c1) +ℚ (a2 *ℚ c2))
dotAddRight a0 a1 a2 b0 b1 b2 c0 c1 c2 =
  solve 9
    (λ a0' a1' a2' b0' b1' b2' c0' c1' c2' →
      (a0' :* (b0' :+ c0')) :+ (a1' :* (b1' :+ c1')) :+ (a2' :* (b2' :+ c2'))
      :=
      ((a0' :* b0') :+ (a1' :* b1') :+ (a2' :* b2')) :+
      ((a0' :* c0') :+ (a1' :* c1') :+ (a2' :* c2')))
    refl a0 a1 a2 b0 b1 b2 c0 c1 c2

dotScaleLeft : (q a0 a1 a2 b0 b1 b2 : ℚ) →
  ((q *ℚ a0) *ℚ b0) +ℚ ((q *ℚ a1) *ℚ b1) +ℚ ((q *ℚ a2) *ℚ b2)
  ≡ q *ℚ ((a0 *ℚ b0) +ℚ (a1 *ℚ b1) +ℚ (a2 *ℚ b2))
dotScaleLeft q a0 a1 a2 b0 b1 b2 =
  solve 7
    (λ q' a0' a1' a2' b0' b1' b2' →
      ((q' :* a0') :* b0') :+ ((q' :* a1') :* b1') :+ ((q' :* a2') :* b2')
      := q' :* ((a0' :* b0') :+ (a1' :* b1') :+ (a2' :* b2')))
    refl q a0 a1 a2 b0 b1 b2

dotScaleRight : (q a0 a1 a2 b0 b1 b2 : ℚ) →
  (a0 *ℚ (q *ℚ b0)) +ℚ (a1 *ℚ (q *ℚ b1)) +ℚ (a2 *ℚ (q *ℚ b2))
  ≡ q *ℚ ((a0 *ℚ b0) +ℚ (a1 *ℚ b1) +ℚ (a2 *ℚ b2))
dotScaleRight q a0 a1 a2 b0 b1 b2 =
  solve 7
    (λ q' a0' a1' a2' b0' b1' b2' →
      (a0' :* (q' :* b0')) :+ (a1' :* (q' :* b1')) :+ (a2' :* (q' :* b2'))
      := q' :* ((a0' :* b0') :+ (a1' :* b1') :+ (a2' :* b2')))
    refl q a0 a1 a2 b0 b1 b2

mulM-addˡ : (A B C : R.QMatrix3) →
  R.mulM (R.addM A B) C ≡ R.addM (R.mulM A C) (R.mulM B C)
mulM-addˡ A B C =
  Basic.qmatrix3Ext
    (dotAddLeft (R.m00 A) (R.m01 A) (R.m02 A) (R.m00 B) (R.m01 B) (R.m02 B) (R.m00 C) (R.m10 C) (R.m20 C))
    (dotAddLeft (R.m00 A) (R.m01 A) (R.m02 A) (R.m00 B) (R.m01 B) (R.m02 B) (R.m01 C) (R.m11 C) (R.m21 C))
    (dotAddLeft (R.m00 A) (R.m01 A) (R.m02 A) (R.m00 B) (R.m01 B) (R.m02 B) (R.m02 C) (R.m12 C) (R.m22 C))
    (dotAddLeft (R.m10 A) (R.m11 A) (R.m12 A) (R.m10 B) (R.m11 B) (R.m12 B) (R.m00 C) (R.m10 C) (R.m20 C))
    (dotAddLeft (R.m10 A) (R.m11 A) (R.m12 A) (R.m10 B) (R.m11 B) (R.m12 B) (R.m01 C) (R.m11 C) (R.m21 C))
    (dotAddLeft (R.m10 A) (R.m11 A) (R.m12 A) (R.m10 B) (R.m11 B) (R.m12 B) (R.m02 C) (R.m12 C) (R.m22 C))
    (dotAddLeft (R.m20 A) (R.m21 A) (R.m22 A) (R.m20 B) (R.m21 B) (R.m22 B) (R.m00 C) (R.m10 C) (R.m20 C))
    (dotAddLeft (R.m20 A) (R.m21 A) (R.m22 A) (R.m20 B) (R.m21 B) (R.m22 B) (R.m01 C) (R.m11 C) (R.m21 C))
    (dotAddLeft (R.m20 A) (R.m21 A) (R.m22 A) (R.m20 B) (R.m21 B) (R.m22 B) (R.m02 C) (R.m12 C) (R.m22 C))

mulM-addʳ : (A B C : R.QMatrix3) →
  R.mulM A (R.addM B C) ≡ R.addM (R.mulM A B) (R.mulM A C)
mulM-addʳ A B C =
  Basic.qmatrix3Ext
    (dotAddRight (R.m00 A) (R.m01 A) (R.m02 A) (R.m00 B) (R.m10 B) (R.m20 B) (R.m00 C) (R.m10 C) (R.m20 C))
    (dotAddRight (R.m00 A) (R.m01 A) (R.m02 A) (R.m01 B) (R.m11 B) (R.m21 B) (R.m01 C) (R.m11 C) (R.m21 C))
    (dotAddRight (R.m00 A) (R.m01 A) (R.m02 A) (R.m02 B) (R.m12 B) (R.m22 B) (R.m02 C) (R.m12 C) (R.m22 C))
    (dotAddRight (R.m10 A) (R.m11 A) (R.m12 A) (R.m00 B) (R.m10 B) (R.m20 B) (R.m00 C) (R.m10 C) (R.m20 C))
    (dotAddRight (R.m10 A) (R.m11 A) (R.m12 A) (R.m01 B) (R.m11 B) (R.m21 B) (R.m01 C) (R.m11 C) (R.m21 C))
    (dotAddRight (R.m10 A) (R.m11 A) (R.m12 A) (R.m02 B) (R.m12 B) (R.m22 B) (R.m02 C) (R.m12 C) (R.m22 C))
    (dotAddRight (R.m20 A) (R.m21 A) (R.m22 A) (R.m00 B) (R.m10 B) (R.m20 B) (R.m00 C) (R.m10 C) (R.m20 C))
    (dotAddRight (R.m20 A) (R.m21 A) (R.m22 A) (R.m01 B) (R.m11 B) (R.m21 B) (R.m01 C) (R.m11 C) (R.m21 C))
    (dotAddRight (R.m20 A) (R.m21 A) (R.m22 A) (R.m02 B) (R.m12 B) (R.m22 B) (R.m02 C) (R.m12 C) (R.m22 C))

mulM-scaleˡ : (q : ℚ) → (A B : R.QMatrix3) →
  R.mulM (R.scaleM q A) B ≡ R.scaleM q (R.mulM A B)
mulM-scaleˡ q A B =
  Basic.qmatrix3Ext
    (dotScaleLeft q (R.m00 A) (R.m01 A) (R.m02 A) (R.m00 B) (R.m10 B) (R.m20 B))
    (dotScaleLeft q (R.m00 A) (R.m01 A) (R.m02 A) (R.m01 B) (R.m11 B) (R.m21 B))
    (dotScaleLeft q (R.m00 A) (R.m01 A) (R.m02 A) (R.m02 B) (R.m12 B) (R.m22 B))
    (dotScaleLeft q (R.m10 A) (R.m11 A) (R.m12 A) (R.m00 B) (R.m10 B) (R.m20 B))
    (dotScaleLeft q (R.m10 A) (R.m11 A) (R.m12 A) (R.m01 B) (R.m11 B) (R.m21 B))
    (dotScaleLeft q (R.m10 A) (R.m11 A) (R.m12 A) (R.m02 B) (R.m12 B) (R.m22 B))
    (dotScaleLeft q (R.m20 A) (R.m21 A) (R.m22 A) (R.m00 B) (R.m10 B) (R.m20 B))
    (dotScaleLeft q (R.m20 A) (R.m21 A) (R.m22 A) (R.m01 B) (R.m11 B) (R.m21 B))
    (dotScaleLeft q (R.m20 A) (R.m21 A) (R.m22 A) (R.m02 B) (R.m12 B) (R.m22 B))

mulM-scaleʳ : (q : ℚ) → (A B : R.QMatrix3) →
  R.mulM A (R.scaleM q B) ≡ R.scaleM q (R.mulM A B)
mulM-scaleʳ q A B =
  Basic.qmatrix3Ext
    (dotScaleRight q (R.m00 A) (R.m01 A) (R.m02 A) (R.m00 B) (R.m10 B) (R.m20 B))
    (dotScaleRight q (R.m00 A) (R.m01 A) (R.m02 A) (R.m01 B) (R.m11 B) (R.m21 B))
    (dotScaleRight q (R.m00 A) (R.m01 A) (R.m02 A) (R.m02 B) (R.m12 B) (R.m22 B))
    (dotScaleRight q (R.m10 A) (R.m11 A) (R.m12 A) (R.m00 B) (R.m10 B) (R.m20 B))
    (dotScaleRight q (R.m10 A) (R.m11 A) (R.m12 A) (R.m01 B) (R.m11 B) (R.m21 B))
    (dotScaleRight q (R.m10 A) (R.m11 A) (R.m12 A) (R.m02 B) (R.m12 B) (R.m22 B))
    (dotScaleRight q (R.m20 A) (R.m21 A) (R.m22 A) (R.m00 B) (R.m10 B) (R.m20 B))
    (dotScaleRight q (R.m20 A) (R.m21 A) (R.m22 A) (R.m01 B) (R.m11 B) (R.m21 B))
    (dotScaleRight q (R.m20 A) (R.m21 A) (R.m22 A) (R.m02 B) (R.m12 B) (R.m22 B))

traceM-add : (A B : R.QMatrix3) →
  R.traceM (R.addM A B) ≡ R.traceM A +ℚ R.traceM B
traceM-add A B =
  solve 6
    (λ a b c d e f → (a :+ d) :+ (b :+ e) :+ (c :+ f) := (a :+ b :+ c) :+ (d :+ e :+ f))
    refl (R.m00 A) (R.m11 A) (R.m22 A) (R.m00 B) (R.m11 B) (R.m22 B)

traceM-scale : (q : ℚ) → (A : R.QMatrix3) →
  R.traceM (R.scaleM q A) ≡ q *ℚ R.traceM A
traceM-scale q A =
  solve 4
    (λ q' a b c → (q' :* a) :+ (q' :* b) :+ (q' :* c) := q' :* (a :+ b :+ c))
    refl q (R.m00 A) (R.m11 A) (R.m22 A)

halfRepack4 : (A B C D : R.QMatrix3) →
  R.scaleM R.halfℚ (R.addM (R.addM A B) (R.addM C D))
  ≡ R.addM (R.scaleM R.halfℚ (R.addM A C)) (R.scaleM R.halfℚ (R.addM B D))
halfRepack4 A B C D =
  Basic.qmatrix3Ext
    (solve 4 (λ a b c d → con R.halfℚ :* ((a :+ b) :+ (c :+ d)) := (con R.halfℚ :* (a :+ c)) :+ (con R.halfℚ :* (b :+ d))) refl (R.m00 A) (R.m00 B) (R.m00 C) (R.m00 D))
    (solve 4 (λ a b c d → con R.halfℚ :* ((a :+ b) :+ (c :+ d)) := (con R.halfℚ :* (a :+ c)) :+ (con R.halfℚ :* (b :+ d))) refl (R.m01 A) (R.m01 B) (R.m01 C) (R.m01 D))
    (solve 4 (λ a b c d → con R.halfℚ :* ((a :+ b) :+ (c :+ d)) := (con R.halfℚ :* (a :+ c)) :+ (con R.halfℚ :* (b :+ d))) refl (R.m02 A) (R.m02 B) (R.m02 C) (R.m02 D))
    (solve 4 (λ a b c d → con R.halfℚ :* ((a :+ b) :+ (c :+ d)) := (con R.halfℚ :* (a :+ c)) :+ (con R.halfℚ :* (b :+ d))) refl (R.m10 A) (R.m10 B) (R.m10 C) (R.m10 D))
    (solve 4 (λ a b c d → con R.halfℚ :* ((a :+ b) :+ (c :+ d)) := (con R.halfℚ :* (a :+ c)) :+ (con R.halfℚ :* (b :+ d))) refl (R.m11 A) (R.m11 B) (R.m11 C) (R.m11 D))
    (solve 4 (λ a b c d → con R.halfℚ :* ((a :+ b) :+ (c :+ d)) := (con R.halfℚ :* (a :+ c)) :+ (con R.halfℚ :* (b :+ d))) refl (R.m12 A) (R.m12 B) (R.m12 C) (R.m12 D))
    (solve 4 (λ a b c d → con R.halfℚ :* ((a :+ b) :+ (c :+ d)) := (con R.halfℚ :* (a :+ c)) :+ (con R.halfℚ :* (b :+ d))) refl (R.m20 A) (R.m20 B) (R.m20 C) (R.m20 D))
    (solve 4 (λ a b c d → con R.halfℚ :* ((a :+ b) :+ (c :+ d)) := (con R.halfℚ :* (a :+ c)) :+ (con R.halfℚ :* (b :+ d))) refl (R.m21 A) (R.m21 B) (R.m21 C) (R.m21 D))
    (solve 4 (λ a b c d → con R.halfℚ :* ((a :+ b) :+ (c :+ d)) := (con R.halfℚ :* (a :+ c)) :+ (con R.halfℚ :* (b :+ d))) refl (R.m22 A) (R.m22 B) (R.m22 C) (R.m22 D))

halfPullScale : (q : ℚ) → (A B : R.QMatrix3) →
  R.scaleM R.halfℚ (R.addM (R.scaleM q A) (R.scaleM q B))
  ≡ R.scaleM q (R.scaleM R.halfℚ (R.addM A B))
halfPullScale q A B =
  Basic.qmatrix3Ext
    (solve 3 (λ q' a b → con R.halfℚ :* ((q' :* a) :+ (q' :* b)) := q' :* (con R.halfℚ :* (a :+ b))) refl q (R.m00 A) (R.m00 B))
    (solve 3 (λ q' a b → con R.halfℚ :* ((q' :* a) :+ (q' :* b)) := q' :* (con R.halfℚ :* (a :+ b))) refl q (R.m01 A) (R.m01 B))
    (solve 3 (λ q' a b → con R.halfℚ :* ((q' :* a) :+ (q' :* b)) := q' :* (con R.halfℚ :* (a :+ b))) refl q (R.m02 A) (R.m02 B))
    (solve 3 (λ q' a b → con R.halfℚ :* ((q' :* a) :+ (q' :* b)) := q' :* (con R.halfℚ :* (a :+ b))) refl q (R.m10 A) (R.m10 B))
    (solve 3 (λ q' a b → con R.halfℚ :* ((q' :* a) :+ (q' :* b)) := q' :* (con R.halfℚ :* (a :+ b))) refl q (R.m11 A) (R.m11 B))
    (solve 3 (λ q' a b → con R.halfℚ :* ((q' :* a) :+ (q' :* b)) := q' :* (con R.halfℚ :* (a :+ b))) refl q (R.m12 A) (R.m12 B))
    (solve 3 (λ q' a b → con R.halfℚ :* ((q' :* a) :+ (q' :* b)) := q' :* (con R.halfℚ :* (a :+ b))) refl q (R.m20 A) (R.m20 B))
    (solve 3 (λ q' a b → con R.halfℚ :* ((q' :* a) :+ (q' :* b)) := q' :* (con R.halfℚ :* (a :+ b))) refl q (R.m21 A) (R.m21 B))
    (solve 3 (λ q' a b → con R.halfℚ :* ((q' :* a) :+ (q' :* b)) := q' :* (con R.halfℚ :* (a :+ b))) refl q (R.m22 A) (R.m22 B))

bulletM-addˡ : (A B C : R.QMatrix3) →
  R.bulletM (R.addM A B) C ≡ R.addM (R.bulletM A C) (R.bulletM B C)
bulletM-addˡ A B C
  rewrite mulM-addˡ A B C | mulM-addʳ C A B =
  halfRepack4 (R.mulM A C) (R.mulM B C) (R.mulM C A) (R.mulM C B)

bulletM-scaleˡ : (q : ℚ) → (A C : R.QMatrix3) →
  R.bulletM (R.scaleM q A) C ≡ R.scaleM q (R.bulletM A C)
bulletM-scaleˡ q A C
  rewrite mulM-scaleˡ q A C | mulM-scaleʳ q C A =
  halfPullScale q (R.mulM A C) (R.mulM C A)

barEntryAdd : (delta ta tb a b : ℚ) →
  R.halfℚ *ℚ (((ta +ℚ tb) *ℚ delta) -ℚ (a +ℚ b))
  ≡
  (R.halfℚ *ℚ ((ta *ℚ delta) -ℚ a)) +ℚ
  (R.halfℚ *ℚ ((tb *ℚ delta) -ℚ b))
barEntryAdd delta ta tb a b =
  solve 5
    (λ d x y u v → con R.halfℚ :* (((x :+ y) :* d) :- (u :+ v)) := (con R.halfℚ :* ((x :* d) :- u)) :+ (con R.halfℚ :* ((y :* d) :- v)))
    refl delta ta tb a b

barEntryScale : (q delta ta a : ℚ) →
  R.halfℚ *ℚ (((q *ℚ ta) *ℚ delta) -ℚ (q *ℚ a))
  ≡ q *ℚ (R.halfℚ *ℚ ((ta *ℚ delta) -ℚ a))
barEntryScale q delta ta a =
  solve 4
    (λ q' d t x → con R.halfℚ :* (((q' :* t) :* d) :- (q' :* x)) := q' :* (con R.halfℚ :* ((t :* d) :- x)))
    refl q delta ta a

barM-add : (A B : R.QMatrix3) → R.barM (R.addM A B) ≡ R.addM (R.barM A) (R.barM B)
barM-add A B rewrite traceM-add A B =
  Basic.qmatrix3Ext
    (barEntryAdd oneℚ (R.traceM A) (R.traceM B) (R.m00 A) (R.m00 B))
    (barEntryAdd zeroℚ (R.traceM A) (R.traceM B) (R.m01 A) (R.m01 B))
    (barEntryAdd zeroℚ (R.traceM A) (R.traceM B) (R.m02 A) (R.m02 B))
    (barEntryAdd zeroℚ (R.traceM A) (R.traceM B) (R.m10 A) (R.m10 B))
    (barEntryAdd oneℚ (R.traceM A) (R.traceM B) (R.m11 A) (R.m11 B))
    (barEntryAdd zeroℚ (R.traceM A) (R.traceM B) (R.m12 A) (R.m12 B))
    (barEntryAdd zeroℚ (R.traceM A) (R.traceM B) (R.m20 A) (R.m20 B))
    (barEntryAdd zeroℚ (R.traceM A) (R.traceM B) (R.m21 A) (R.m21 B))
    (barEntryAdd oneℚ (R.traceM A) (R.traceM B) (R.m22 A) (R.m22 B))

barM-scale : (q : ℚ) → (A : R.QMatrix3) → R.barM (R.scaleM q A) ≡ R.scaleM q (R.barM A)
barM-scale q A rewrite traceM-scale q A =
  Basic.qmatrix3Ext
    (barEntryScale q oneℚ (R.traceM A) (R.m00 A))
    (barEntryScale q zeroℚ (R.traceM A) (R.m01 A))
    (barEntryScale q zeroℚ (R.traceM A) (R.m02 A))
    (barEntryScale q zeroℚ (R.traceM A) (R.m10 A))
    (barEntryScale q oneℚ (R.traceM A) (R.m11 A))
    (barEntryScale q zeroℚ (R.traceM A) (R.m12 A))
    (barEntryScale q zeroℚ (R.traceM A) (R.m20 A))
    (barEntryScale q zeroℚ (R.traceM A) (R.m21 A))
    (barEntryScale q oneℚ (R.traceM A) (R.m22 A))

crossEntryAdd : (delta ba bb ta tb tc a b c tba tbb : ℚ) →
  (((ba +ℚ bb) -ℚ ((R.halfℚ *ℚ (ta +ℚ tb)) *ℚ c)) -ℚ ((R.halfℚ *ℚ tc) *ℚ (a +ℚ b))) +ℚ
  ((R.halfℚ *ℚ (((ta +ℚ tb) *ℚ tc) -ℚ (tba +ℚ tbb))) *ℚ delta)
  ≡
  ((((ba -ℚ ((R.halfℚ *ℚ ta) *ℚ c)) -ℚ ((R.halfℚ *ℚ tc) *ℚ a)) +ℚ
    ((R.halfℚ *ℚ ((ta *ℚ tc) -ℚ tba)) *ℚ delta)) +ℚ
   (((bb -ℚ ((R.halfℚ *ℚ tb) *ℚ c)) -ℚ ((R.halfℚ *ℚ tc) *ℚ b)) +ℚ
    ((R.halfℚ *ℚ ((tb *ℚ tc) -ℚ tbb)) *ℚ delta)))
crossEntryAdd delta ba bb ta tb tc a b c tba tbb =
  solve 11
    (λ d x y u v w a' b' c' p q →
      (((x :+ y) :- ((con R.halfℚ :* (u :+ v)) :* c')) :- ((con R.halfℚ :* w) :* (a' :+ b'))) :+
      ((con R.halfℚ :* (((u :+ v) :* w) :- (p :+ q))) :* d)
      :=
      (((x :- ((con R.halfℚ :* u) :* c')) :- ((con R.halfℚ :* w) :* a')) :+ ((con R.halfℚ :* ((u :* w) :- p)) :* d)) :+
      (((y :- ((con R.halfℚ :* v) :* c')) :- ((con R.halfℚ :* w) :* b')) :+ ((con R.halfℚ :* ((v :* w) :- q)) :* d)))
    refl delta ba bb ta tb tc a b c tba tbb

crossEntryScale : (q delta ba ta tc a c tba : ℚ) →
  (((q *ℚ ba) -ℚ ((R.halfℚ *ℚ (q *ℚ ta)) *ℚ c)) -ℚ ((R.halfℚ *ℚ tc) *ℚ (q *ℚ a))) +ℚ
  ((R.halfℚ *ℚ (((q *ℚ ta) *ℚ tc) -ℚ (q *ℚ tba))) *ℚ delta)
  ≡
  q *ℚ (((ba -ℚ ((R.halfℚ *ℚ ta) *ℚ c)) -ℚ ((R.halfℚ *ℚ tc) *ℚ a)) +ℚ
    ((R.halfℚ *ℚ ((ta *ℚ tc) -ℚ tba)) *ℚ delta))
crossEntryScale q delta ba ta tc a c tba =
  solve 8
    (λ q' d x u w a' c' p →
      (((q' :* x) :- ((con R.halfℚ :* (q' :* u)) :* c')) :- ((con R.halfℚ :* w) :* (q' :* a'))) :+
      ((con R.halfℚ :* (((q' :* u) :* w) :- (q' :* p))) :* d)
      :=
      q' :* (((x :- ((con R.halfℚ :* u) :* c')) :- ((con R.halfℚ :* w) :* a')) :+ ((con R.halfℚ :* ((u :* w) :- p)) :* d)))
    refl q delta ba ta tc a c tba

crossM-addˡ : (A B C : R.QMatrix3) → R.crossM (R.addM A B) C ≡ R.addM (R.crossM A C) (R.crossM B C)
crossM-addˡ A B C
  rewrite bulletM-addˡ A B C | traceM-add A B | traceM-add (R.bulletM A C) (R.bulletM B C) =
  Basic.qmatrix3Ext
    (crossEntryAdd oneℚ (R.m00 (R.bulletM A C)) (R.m00 (R.bulletM B C)) (R.traceM A) (R.traceM B) (R.traceM C) (R.m00 A) (R.m00 B) (R.m00 C) (R.traceM (R.bulletM A C)) (R.traceM (R.bulletM B C)))
    (crossEntryAdd zeroℚ (R.m01 (R.bulletM A C)) (R.m01 (R.bulletM B C)) (R.traceM A) (R.traceM B) (R.traceM C) (R.m01 A) (R.m01 B) (R.m01 C) (R.traceM (R.bulletM A C)) (R.traceM (R.bulletM B C)))
    (crossEntryAdd zeroℚ (R.m02 (R.bulletM A C)) (R.m02 (R.bulletM B C)) (R.traceM A) (R.traceM B) (R.traceM C) (R.m02 A) (R.m02 B) (R.m02 C) (R.traceM (R.bulletM A C)) (R.traceM (R.bulletM B C)))
    (crossEntryAdd zeroℚ (R.m10 (R.bulletM A C)) (R.m10 (R.bulletM B C)) (R.traceM A) (R.traceM B) (R.traceM C) (R.m10 A) (R.m10 B) (R.m10 C) (R.traceM (R.bulletM A C)) (R.traceM (R.bulletM B C)))
    (crossEntryAdd oneℚ (R.m11 (R.bulletM A C)) (R.m11 (R.bulletM B C)) (R.traceM A) (R.traceM B) (R.traceM C) (R.m11 A) (R.m11 B) (R.m11 C) (R.traceM (R.bulletM A C)) (R.traceM (R.bulletM B C)))
    (crossEntryAdd zeroℚ (R.m12 (R.bulletM A C)) (R.m12 (R.bulletM B C)) (R.traceM A) (R.traceM B) (R.traceM C) (R.m12 A) (R.m12 B) (R.m12 C) (R.traceM (R.bulletM A C)) (R.traceM (R.bulletM B C)))
    (crossEntryAdd zeroℚ (R.m20 (R.bulletM A C)) (R.m20 (R.bulletM B C)) (R.traceM A) (R.traceM B) (R.traceM C) (R.m20 A) (R.m20 B) (R.m20 C) (R.traceM (R.bulletM A C)) (R.traceM (R.bulletM B C)))
    (crossEntryAdd zeroℚ (R.m21 (R.bulletM A C)) (R.m21 (R.bulletM B C)) (R.traceM A) (R.traceM B) (R.traceM C) (R.m21 A) (R.m21 B) (R.m21 C) (R.traceM (R.bulletM A C)) (R.traceM (R.bulletM B C)))
    (crossEntryAdd oneℚ (R.m22 (R.bulletM A C)) (R.m22 (R.bulletM B C)) (R.traceM A) (R.traceM B) (R.traceM C) (R.m22 A) (R.m22 B) (R.m22 C) (R.traceM (R.bulletM A C)) (R.traceM (R.bulletM B C)))

crossM-scaleˡ : (q : ℚ) → (A C : R.QMatrix3) → R.crossM (R.scaleM q A) C ≡ R.scaleM q (R.crossM A C)
crossM-scaleˡ q A C
  rewrite bulletM-scaleˡ q A C | traceM-scale q A | traceM-scale q (R.bulletM A C) =
  Basic.qmatrix3Ext
    (crossEntryScale q oneℚ (R.m00 (R.bulletM A C)) (R.traceM A) (R.traceM C) (R.m00 A) (R.m00 C) (R.traceM (R.bulletM A C)))
    (crossEntryScale q zeroℚ (R.m01 (R.bulletM A C)) (R.traceM A) (R.traceM C) (R.m01 A) (R.m01 C) (R.traceM (R.bulletM A C)))
    (crossEntryScale q zeroℚ (R.m02 (R.bulletM A C)) (R.traceM A) (R.traceM C) (R.m02 A) (R.m02 C) (R.traceM (R.bulletM A C)))
    (crossEntryScale q zeroℚ (R.m10 (R.bulletM A C)) (R.traceM A) (R.traceM C) (R.m10 A) (R.m10 C) (R.traceM (R.bulletM A C)))
    (crossEntryScale q oneℚ (R.m11 (R.bulletM A C)) (R.traceM A) (R.traceM C) (R.m11 A) (R.m11 C) (R.traceM (R.bulletM A C)))
    (crossEntryScale q zeroℚ (R.m12 (R.bulletM A C)) (R.traceM A) (R.traceM C) (R.m12 A) (R.m12 C) (R.traceM (R.bulletM A C)))
    (crossEntryScale q zeroℚ (R.m20 (R.bulletM A C)) (R.traceM A) (R.traceM C) (R.m20 A) (R.m20 C) (R.traceM (R.bulletM A C)))
    (crossEntryScale q zeroℚ (R.m21 (R.bulletM A C)) (R.traceM A) (R.traceM C) (R.m21 A) (R.m21 C) (R.traceM (R.bulletM A C)))
    (crossEntryScale q oneℚ (R.m22 (R.bulletM A C)) (R.traceM A) (R.traceM C) (R.m22 A) (R.m22 C) (R.traceM (R.bulletM A C)))

repack6A : (A B C D E F : R.QMatrix3) →
  R.addM (R.addM A D) (R.addM (R.addM B E) (R.addM C F))
  ≡ R.addM (R.addM A (R.addM B C)) (R.addM D (R.addM E F))
repack6A A B C D E F =
  Basic.qmatrix3Ext
    (solve 6 (λ a b c d e f → (a :+ d) :+ ((b :+ e) :+ (c :+ f)) := (a :+ (b :+ c)) :+ (d :+ (e :+ f))) refl (R.m00 A) (R.m00 B) (R.m00 C) (R.m00 D) (R.m00 E) (R.m00 F))
    (solve 6 (λ a b c d e f → (a :+ d) :+ ((b :+ e) :+ (c :+ f)) := (a :+ (b :+ c)) :+ (d :+ (e :+ f))) refl (R.m01 A) (R.m01 B) (R.m01 C) (R.m01 D) (R.m01 E) (R.m01 F))
    (solve 6 (λ a b c d e f → (a :+ d) :+ ((b :+ e) :+ (c :+ f)) := (a :+ (b :+ c)) :+ (d :+ (e :+ f))) refl (R.m02 A) (R.m02 B) (R.m02 C) (R.m02 D) (R.m02 E) (R.m02 F))
    (solve 6 (λ a b c d e f → (a :+ d) :+ ((b :+ e) :+ (c :+ f)) := (a :+ (b :+ c)) :+ (d :+ (e :+ f))) refl (R.m10 A) (R.m10 B) (R.m10 C) (R.m10 D) (R.m10 E) (R.m10 F))
    (solve 6 (λ a b c d e f → (a :+ d) :+ ((b :+ e) :+ (c :+ f)) := (a :+ (b :+ c)) :+ (d :+ (e :+ f))) refl (R.m11 A) (R.m11 B) (R.m11 C) (R.m11 D) (R.m11 E) (R.m11 F))
    (solve 6 (λ a b c d e f → (a :+ d) :+ ((b :+ e) :+ (c :+ f)) := (a :+ (b :+ c)) :+ (d :+ (e :+ f))) refl (R.m12 A) (R.m12 B) (R.m12 C) (R.m12 D) (R.m12 E) (R.m12 F))
    (solve 6 (λ a b c d e f → (a :+ d) :+ ((b :+ e) :+ (c :+ f)) := (a :+ (b :+ c)) :+ (d :+ (e :+ f))) refl (R.m20 A) (R.m20 B) (R.m20 C) (R.m20 D) (R.m20 E) (R.m20 F))
    (solve 6 (λ a b c d e f → (a :+ d) :+ ((b :+ e) :+ (c :+ f)) := (a :+ (b :+ c)) :+ (d :+ (e :+ f))) refl (R.m21 A) (R.m21 B) (R.m21 C) (R.m21 D) (R.m21 E) (R.m21 F))
    (solve 6 (λ a b c d e f → (a :+ d) :+ ((b :+ e) :+ (c :+ f)) := (a :+ (b :+ c)) :+ (d :+ (e :+ f))) refl (R.m22 A) (R.m22 B) (R.m22 C) (R.m22 D) (R.m22 E) (R.m22 F))

repack6B : (A B C D E F : R.QMatrix3) →
  R.addM (R.addM (R.addM A D) (R.addM B E)) (R.addM C F)
  ≡ R.addM (R.addM (R.addM A B) C) (R.addM (R.addM D E) F)
repack6B A B C D E F =
  Basic.qmatrix3Ext
    (solve 6 (λ a b c d e f → ((a :+ d) :+ (b :+ e)) :+ (c :+ f) := ((a :+ b) :+ c) :+ ((d :+ e) :+ f)) refl (R.m00 A) (R.m00 B) (R.m00 C) (R.m00 D) (R.m00 E) (R.m00 F))
    (solve 6 (λ a b c d e f → ((a :+ d) :+ (b :+ e)) :+ (c :+ f) := ((a :+ b) :+ c) :+ ((d :+ e) :+ f)) refl (R.m01 A) (R.m01 B) (R.m01 C) (R.m01 D) (R.m01 E) (R.m01 F))
    (solve 6 (λ a b c d e f → ((a :+ d) :+ (b :+ e)) :+ (c :+ f) := ((a :+ b) :+ c) :+ ((d :+ e) :+ f)) refl (R.m02 A) (R.m02 B) (R.m02 C) (R.m02 D) (R.m02 E) (R.m02 F))
    (solve 6 (λ a b c d e f → ((a :+ d) :+ (b :+ e)) :+ (c :+ f) := ((a :+ b) :+ c) :+ ((d :+ e) :+ f)) refl (R.m10 A) (R.m10 B) (R.m10 C) (R.m10 D) (R.m10 E) (R.m10 F))
    (solve 6 (λ a b c d e f → ((a :+ d) :+ (b :+ e)) :+ (c :+ f) := ((a :+ b) :+ c) :+ ((d :+ e) :+ f)) refl (R.m11 A) (R.m11 B) (R.m11 C) (R.m11 D) (R.m11 E) (R.m11 F))
    (solve 6 (λ a b c d e f → ((a :+ d) :+ (b :+ e)) :+ (c :+ f) := ((a :+ b) :+ c) :+ ((d :+ e) :+ f)) refl (R.m12 A) (R.m12 B) (R.m12 C) (R.m12 D) (R.m12 E) (R.m12 F))
    (solve 6 (λ a b c d e f → ((a :+ d) :+ (b :+ e)) :+ (c :+ f) := ((a :+ b) :+ c) :+ ((d :+ e) :+ f)) refl (R.m20 A) (R.m20 B) (R.m20 C) (R.m20 D) (R.m20 E) (R.m20 F))
    (solve 6 (λ a b c d e f → ((a :+ d) :+ (b :+ e)) :+ (c :+ f) := ((a :+ b) :+ c) :+ ((d :+ e) :+ f)) refl (R.m21 A) (R.m21 B) (R.m21 C) (R.m21 D) (R.m21 E) (R.m21 F))
    (solve 6 (λ a b c d e f → ((a :+ d) :+ (b :+ e)) :+ (c :+ f) := ((a :+ b) :+ c) :+ ((d :+ e) :+ f)) refl (R.m22 A) (R.m22 B) (R.m22 C) (R.m22 D) (R.m22 E) (R.m22 F))

repackScale3A : (q : ℚ) → (A B C : R.QMatrix3) →
  R.addM (R.scaleM q A) (R.addM (R.scaleM q B) (R.scaleM q C))
  ≡ R.scaleM q (R.addM A (R.addM B C))
repackScale3A q A B C =
  Basic.qmatrix3Ext
    (solve 4 (λ q' a b c → (q' :* a) :+ ((q' :* b) :+ (q' :* c)) := q' :* (a :+ (b :+ c))) refl q (R.m00 A) (R.m00 B) (R.m00 C))
    (solve 4 (λ q' a b c → (q' :* a) :+ ((q' :* b) :+ (q' :* c)) := q' :* (a :+ (b :+ c))) refl q (R.m01 A) (R.m01 B) (R.m01 C))
    (solve 4 (λ q' a b c → (q' :* a) :+ ((q' :* b) :+ (q' :* c)) := q' :* (a :+ (b :+ c))) refl q (R.m02 A) (R.m02 B) (R.m02 C))
    (solve 4 (λ q' a b c → (q' :* a) :+ ((q' :* b) :+ (q' :* c)) := q' :* (a :+ (b :+ c))) refl q (R.m10 A) (R.m10 B) (R.m10 C))
    (solve 4 (λ q' a b c → (q' :* a) :+ ((q' :* b) :+ (q' :* c)) := q' :* (a :+ (b :+ c))) refl q (R.m11 A) (R.m11 B) (R.m11 C))
    (solve 4 (λ q' a b c → (q' :* a) :+ ((q' :* b) :+ (q' :* c)) := q' :* (a :+ (b :+ c))) refl q (R.m12 A) (R.m12 B) (R.m12 C))
    (solve 4 (λ q' a b c → (q' :* a) :+ ((q' :* b) :+ (q' :* c)) := q' :* (a :+ (b :+ c))) refl q (R.m20 A) (R.m20 B) (R.m20 C))
    (solve 4 (λ q' a b c → (q' :* a) :+ ((q' :* b) :+ (q' :* c)) := q' :* (a :+ (b :+ c))) refl q (R.m21 A) (R.m21 B) (R.m21 C))
    (solve 4 (λ q' a b c → (q' :* a) :+ ((q' :* b) :+ (q' :* c)) := q' :* (a :+ (b :+ c))) refl q (R.m22 A) (R.m22 B) (R.m22 C))

repackScale3B : (q : ℚ) → (A B C : R.QMatrix3) →
  R.addM (R.addM (R.scaleM q A) (R.scaleM q B)) (R.scaleM q C)
  ≡ R.scaleM q (R.addM (R.addM A B) C)
repackScale3B q A B C =
  Basic.qmatrix3Ext
    (solve 4 (λ q' a b c → ((q' :* a) :+ (q' :* b)) :+ (q' :* c) := q' :* ((a :+ b) :+ c)) refl q (R.m00 A) (R.m00 B) (R.m00 C))
    (solve 4 (λ q' a b c → ((q' :* a) :+ (q' :* b)) :+ (q' :* c) := q' :* ((a :+ b) :+ c)) refl q (R.m01 A) (R.m01 B) (R.m01 C))
    (solve 4 (λ q' a b c → ((q' :* a) :+ (q' :* b)) :+ (q' :* c) := q' :* ((a :+ b) :+ c)) refl q (R.m02 A) (R.m02 B) (R.m02 C))
    (solve 4 (λ q' a b c → ((q' :* a) :+ (q' :* b)) :+ (q' :* c) := q' :* ((a :+ b) :+ c)) refl q (R.m10 A) (R.m10 B) (R.m10 C))
    (solve 4 (λ q' a b c → ((q' :* a) :+ (q' :* b)) :+ (q' :* c) := q' :* ((a :+ b) :+ c)) refl q (R.m11 A) (R.m11 B) (R.m11 C))
    (solve 4 (λ q' a b c → ((q' :* a) :+ (q' :* b)) :+ (q' :* c) := q' :* ((a :+ b) :+ c)) refl q (R.m12 A) (R.m12 B) (R.m12 C))
    (solve 4 (λ q' a b c → ((q' :* a) :+ (q' :* b)) :+ (q' :* c) := q' :* ((a :+ b) :+ c)) refl q (R.m20 A) (R.m20 B) (R.m20 C))
    (solve 4 (λ q' a b c → ((q' :* a) :+ (q' :* b)) :+ (q' :* c) := q' :* ((a :+ b) :+ c)) refl q (R.m21 A) (R.m21 B) (R.m21 C))
    (solve 4 (λ q' a b c → ((q' :* a) :+ (q' :* b)) :+ (q' :* c) := q' :* ((a :+ b) :+ c)) refl q (R.m22 A) (R.m22 B) (R.m22 C))

leftAdditiveWitness : Laws.LeftAdditive
leftAdditiveWitness
  (R.rationalFirstTits27 A B C)
  (R.rationalFirstTits27 D E F)
  (R.rationalFirstTits27 G H I)
  rewrite bulletM-addˡ A D G
        | mulM-addˡ B E I | barM-add (R.mulM B I) (R.mulM E I)
        | mulM-addʳ H C F | barM-add (R.mulM H C) (R.mulM H F)
        | barM-add A D | mulM-addˡ (R.barM A) (R.barM D) H
        | mulM-addʳ (R.barM G) B E
        | crossM-addˡ C F I
        | mulM-addʳ I (R.barM A) (R.barM D)
        | mulM-addˡ C F (R.barM G)
        | crossM-addˡ B E H =
  Basic.firstTits27Ext
    (repack6A
      (R.bulletM A G)
      (R.barM (R.mulM B I))
      (R.barM (R.mulM H C))
      (R.bulletM D G)
      (R.barM (R.mulM E I))
      (R.barM (R.mulM H F)))
    (repack6B
      (R.mulM (R.barM A) H)
      (R.mulM (R.barM G) B)
      (R.crossM C I)
      (R.mulM (R.barM D) H)
      (R.mulM (R.barM G) E)
      (R.crossM F I))
    (repack6B
      (R.mulM I (R.barM A))
      (R.mulM C (R.barM G))
      (R.crossM B H)
      (R.mulM I (R.barM D))
      (R.mulM F (R.barM G))
      (R.crossM E H))

leftHomogeneousWitness : Laws.LeftHomogeneous
leftHomogeneousWitness q (R.rationalFirstTits27 A B C) (R.rationalFirstTits27 G H I)
  rewrite bulletM-scaleˡ q A G
        | mulM-scaleˡ q B I | barM-scale q (R.mulM B I)
        | mulM-scaleʳ q H C | barM-scale q (R.mulM H C)
        | barM-scale q A | mulM-scaleˡ q (R.barM A) H
        | mulM-scaleʳ q (R.barM G) B
        | crossM-scaleˡ q C I
        | mulM-scaleʳ q I (R.barM A)
        | mulM-scaleˡ q C (R.barM G)
        | crossM-scaleˡ q B H =
  Basic.firstTits27Ext
    (repackScale3A q
      (R.bulletM A G)
      (R.barM (R.mulM B I))
      (R.barM (R.mulM H C)))
    (repackScale3B q
      (R.mulM (R.barM A) H)
      (R.mulM (R.barM G) B)
      (R.crossM C I))
    (repackScale3B q
      (R.mulM I (R.barM A))
      (R.mulM C (R.barM G))
      (R.crossM B H))

addJ-cong : {A A' B B' : R.RationalFirstTits27} → A ≡ A' → B ≡ B' → R.addJ A B ≡ R.addJ A' B'
addJ-cong refl refl = refl

scaleJ-cong : (q : ℚ) → {A B : R.RationalFirstTits27} → A ≡ B → R.scaleJ q A ≡ R.scaleJ q B
scaleJ-cong q refl = refl

rightAdditiveWitness : Laws.RightAdditive
rightAdditiveWitness X Y Z =
  trans
    (Basic.commutativeWitness X (R.addJ Y Z))
    (trans
      (leftAdditiveWitness Y Z X)
      (addJ-cong (Basic.commutativeWitness Y X) (Basic.commutativeWitness Z X)))

rightHomogeneousWitness : Laws.RightHomogeneous
rightHomogeneousWitness q X Y =
  trans
    (Basic.commutativeWitness X (R.scaleJ q Y))
    (trans
      (leftHomogeneousWitness q Y X)
      (scaleJ-cong q (Basic.commutativeWitness Y X)))

record RationalFirstTitsBilinearityWitnesses : Set where
  constructor rational-first-tits-bilinearity-witnesses
  field
    leftAdditive : Laws.LeftAdditive
    rightAdditive : Laws.RightAdditive
    leftHomogeneous : Laws.LeftHomogeneous
    rightHomogeneous : Laws.RightHomogeneous
open RationalFirstTitsBilinearityWitnesses public

canonicalBilinearityWitnesses : RationalFirstTitsBilinearityWitnesses
canonicalBilinearityWitnesses =
  rational-first-tits-bilinearity-witnesses
    leftAdditiveWitness rightAdditiveWitness leftHomogeneousWitness rightHomogeneousWitness

record BilinearityBoundary : Set where
  constructor bilinearity-boundary
  field
    matrixAddScaleLinearitySourceWritten : Bool
    matrixMultiplicationBilinearitySourceWritten : Bool
    traceLinearitySourceWritten : Bool
    bulletBarCrossLinearitySourceWritten : Bool
    fullFirstTitsBilinearityTermSourceWritten : Bool
    externalAlbertClassificationUsed : Bool
    exactHeadAgdaKernelReceiptPresent : Bool
    boundary : String
open BilinearityBoundary public

canonicalBoundary : BilinearityBoundary
canonicalBoundary =
  bilinearity-boundary
    true true true true true false false
    "All four bilinearity witnesses for the literal rational M3(Q)^3 first-Tits product are source-written by reducing matrix multiplication, trace, bullet, bar and cross to the repository's rational polynomial solver. Commutativity is used only to derive right-linearity from left-linearity. No Albert/F4/E6 classification theorem is consumed. Exact-head kernel payment remains separate."
