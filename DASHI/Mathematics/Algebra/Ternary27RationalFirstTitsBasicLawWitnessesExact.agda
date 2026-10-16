module DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsBasicLawWitnessesExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Data.Rational.Solver using (module +-*-Solver)
import Data.Rational.Properties as Rₚ

open +-*-Solver using (solve; _:+_; _:-_; _:*_; con; _:=_)
open import DASHI.Core.Q using (ℚ; _-ℚ_; _*ℚ_; zeroℚ; oneℚ)
import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsCarrierExact as R
import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsLawObligationsExact as Laws

------------------------------------------------------------------------
-- PROOF-RELEVANT BASIC LAW SLICE FOR THE LITERAL RATIONAL FIRST-TITS CARRIER
--
-- All witnesses below are built from the literal M3(Q)^3 definitions and the
-- repository's already-used Data.Rational.Solver.  External Albert/F4/E6
-- classification is not used to manufacture a local algebra law.
--
-- Source-written here:
--   * product commutativity;
--   * left/right unit;
--   * cubic(unit)=1.
--
-- Still deliberately open here:
--   * full bilinearity package;
--   * cubic homogeneity;
--   * Jordan identity;
--   * complete PaidRationalFirstTitsLaws inhabitant.
--
-- No exact-head kernel-green claim is made without an Agda execution receipt.
------------------------------------------------------------------------

qmatrix3Ext :
  {A B : R.QMatrix3} →
  R.m00 A ≡ R.m00 B → R.m01 A ≡ R.m01 B → R.m02 A ≡ R.m02 B →
  R.m10 A ≡ R.m10 B → R.m11 A ≡ R.m11 B → R.m12 A ≡ R.m12 B →
  R.m20 A ≡ R.m20 B → R.m21 A ≡ R.m21 B → R.m22 A ≡ R.m22 B →
  A ≡ B
qmatrix3Ext
  {R.qmatrix3 a00 a01 a02 a10 a11 a12 a20 a21 a22}
  {R.qmatrix3 b00 b01 b02 b10 b11 b12 b20 b21 b22}
  refl refl refl refl refl refl refl refl refl = refl

firstTits27Ext :
  {X Y : R.RationalFirstTits27} →
  R.block0 X ≡ R.block0 Y →
  R.block1 X ≡ R.block1 Y →
  R.block2 X ≡ R.block2 Y →
  X ≡ Y
firstTits27Ext
  {R.rationalFirstTits27 a b c}
  {R.rationalFirstTits27 d e f}
  refl refl refl = refl

addM-cong :
  {A A' B B' : R.QMatrix3} →
  A ≡ A' → B ≡ B' → R.addM A B ≡ R.addM A' B'
addM-cong refl refl = refl

scaleM-cong-matrix :
  (q : ℚ) → {A B : R.QMatrix3} → A ≡ B → R.scaleM q A ≡ R.scaleM q B
scaleM-cong-matrix q refl = refl

scaleM-cong-scalar :
  {q r : ℚ} → q ≡ r → (A : R.QMatrix3) → R.scaleM q A ≡ R.scaleM r A
scaleM-cong-scalar refl A = refl

traceM-cong : {A B : R.QMatrix3} → A ≡ B → R.traceM A ≡ R.traceM B
traceM-cong refl = refl

addM-comm : (A B : R.QMatrix3) → R.addM A B ≡ R.addM B A
addM-comm A B =
  qmatrix3Ext
    (Rₚ.+-comm (R.m00 A) (R.m00 B))
    (Rₚ.+-comm (R.m01 A) (R.m01 B))
    (Rₚ.+-comm (R.m02 A) (R.m02 B))
    (Rₚ.+-comm (R.m10 A) (R.m10 B))
    (Rₚ.+-comm (R.m11 A) (R.m11 B))
    (Rₚ.+-comm (R.m12 A) (R.m12 B))
    (Rₚ.+-comm (R.m20 A) (R.m20 B))
    (Rₚ.+-comm (R.m21 A) (R.m21 B))
    (Rₚ.+-comm (R.m22 A) (R.m22 B))

addM-zeroˡ : (A : R.QMatrix3) → R.addM R.zeroM A ≡ A
addM-zeroˡ A =
  qmatrix3Ext
    (solve 1 (λ x → con zeroℚ :+ x := x) refl (R.m00 A))
    (solve 1 (λ x → con zeroℚ :+ x := x) refl (R.m01 A))
    (solve 1 (λ x → con zeroℚ :+ x := x) refl (R.m02 A))
    (solve 1 (λ x → con zeroℚ :+ x := x) refl (R.m10 A))
    (solve 1 (λ x → con zeroℚ :+ x := x) refl (R.m11 A))
    (solve 1 (λ x → con zeroℚ :+ x := x) refl (R.m12 A))
    (solve 1 (λ x → con zeroℚ :+ x := x) refl (R.m20 A))
    (solve 1 (λ x → con zeroℚ :+ x := x) refl (R.m21 A))
    (solve 1 (λ x → con zeroℚ :+ x := x) refl (R.m22 A))

addM-zeroʳ : (A : R.QMatrix3) → R.addM A R.zeroM ≡ A
addM-zeroʳ A = trans (addM-comm A R.zeroM) (addM-zeroˡ A)

subM-zero-zero : R.subM R.zeroM R.zeroM ≡ R.zeroM
subM-zero-zero =
  qmatrix3Ext
    (solve 0 (λ → con zeroℚ :- con zeroℚ := con zeroℚ) refl)
    (solve 0 (λ → con zeroℚ :- con zeroℚ := con zeroℚ) refl)
    (solve 0 (λ → con zeroℚ :- con zeroℚ := con zeroℚ) refl)
    (solve 0 (λ → con zeroℚ :- con zeroℚ := con zeroℚ) refl)
    (solve 0 (λ → con zeroℚ :- con zeroℚ := con zeroℚ) refl)
    (solve 0 (λ → con zeroℚ :- con zeroℚ := con zeroℚ) refl)
    (solve 0 (λ → con zeroℚ :- con zeroℚ := con zeroℚ) refl)
    (solve 0 (λ → con zeroℚ :- con zeroℚ := con zeroℚ) refl)
    (solve 0 (λ → con zeroℚ :- con zeroℚ := con zeroℚ) refl)

scaleM-zero-scalar : (A : R.QMatrix3) → R.scaleM zeroℚ A ≡ R.zeroM
scaleM-zero-scalar A =
  qmatrix3Ext
    (solve 1 (λ x → con zeroℚ :* x := con zeroℚ) refl (R.m00 A))
    (solve 1 (λ x → con zeroℚ :* x := con zeroℚ) refl (R.m01 A))
    (solve 1 (λ x → con zeroℚ :* x := con zeroℚ) refl (R.m02 A))
    (solve 1 (λ x → con zeroℚ :* x := con zeroℚ) refl (R.m10 A))
    (solve 1 (λ x → con zeroℚ :* x := con zeroℚ) refl (R.m11 A))
    (solve 1 (λ x → con zeroℚ :* x := con zeroℚ) refl (R.m12 A))
    (solve 1 (λ x → con zeroℚ :* x := con zeroℚ) refl (R.m20 A))
    (solve 1 (λ x → con zeroℚ :* x := con zeroℚ) refl (R.m21 A))
    (solve 1 (λ x → con zeroℚ :* x := con zeroℚ) refl (R.m22 A))

scaleM-zero-matrix : (q : ℚ) → R.scaleM q R.zeroM ≡ R.zeroM
scaleM-zero-matrix q =
  qmatrix3Ext
    (solve 1 (λ x → x :* con zeroℚ := con zeroℚ) refl q)
    (solve 1 (λ x → x :* con zeroℚ := con zeroℚ) refl q)
    (solve 1 (λ x → x :* con zeroℚ := con zeroℚ) refl q)
    (solve 1 (λ x → x :* con zeroℚ := con zeroℚ) refl q)
    (solve 1 (λ x → x :* con zeroℚ := con zeroℚ) refl q)
    (solve 1 (λ x → x :* con zeroℚ := con zeroℚ) refl q)
    (solve 1 (λ x → x :* con zeroℚ := con zeroℚ) refl q)
    (solve 1 (λ x → x :* con zeroℚ := con zeroℚ) refl q)
    (solve 1 (λ x → x :* con zeroℚ := con zeroℚ) refl q)

zeroDotLeft : (x y z : ℚ) →
  (zeroℚ *ℚ x) R.+ℚ (zeroℚ *ℚ y) R.+ℚ (zeroℚ *ℚ z) ≡ zeroℚ
zeroDotLeft x y z =
  solve 3
    (λ a b c → (con zeroℚ :* a) :+ (con zeroℚ :* b) :+ (con zeroℚ :* c) := con zeroℚ)
    refl x y z

zeroDotRight : (x y z : ℚ) →
  (x *ℚ zeroℚ) R.+ℚ (y *ℚ zeroℚ) R.+ℚ (z *ℚ zeroℚ) ≡ zeroℚ
zeroDotRight x y z =
  solve 3
    (λ a b c → (a :* con zeroℚ) :+ (b :* con zeroℚ) :+ (c :* con zeroℚ) := con zeroℚ)
    refl x y z

mulM-zeroˡ : (A : R.QMatrix3) → R.mulM R.zeroM A ≡ R.zeroM
mulM-zeroˡ A =
  qmatrix3Ext
    (zeroDotLeft (R.m00 A) (R.m10 A) (R.m20 A))
    (zeroDotLeft (R.m01 A) (R.m11 A) (R.m21 A))
    (zeroDotLeft (R.m02 A) (R.m12 A) (R.m22 A))
    (zeroDotLeft (R.m00 A) (R.m10 A) (R.m20 A))
    (zeroDotLeft (R.m01 A) (R.m11 A) (R.m21 A))
    (zeroDotLeft (R.m02 A) (R.m12 A) (R.m22 A))
    (zeroDotLeft (R.m00 A) (R.m10 A) (R.m20 A))
    (zeroDotLeft (R.m01 A) (R.m11 A) (R.m21 A))
    (zeroDotLeft (R.m02 A) (R.m12 A) (R.m22 A))

mulM-zeroʳ : (A : R.QMatrix3) → R.mulM A R.zeroM ≡ R.zeroM
mulM-zeroʳ A =
  qmatrix3Ext
    (zeroDotRight (R.m00 A) (R.m01 A) (R.m02 A))
    (zeroDotRight (R.m00 A) (R.m01 A) (R.m02 A))
    (zeroDotRight (R.m00 A) (R.m01 A) (R.m02 A))
    (zeroDotRight (R.m10 A) (R.m11 A) (R.m12 A))
    (zeroDotRight (R.m10 A) (R.m11 A) (R.m12 A))
    (zeroDotRight (R.m10 A) (R.m11 A) (R.m12 A))
    (zeroDotRight (R.m20 A) (R.m21 A) (R.m22 A))
    (zeroDotRight (R.m20 A) (R.m21 A) (R.m22 A))
    (zeroDotRight (R.m20 A) (R.m21 A) (R.m22 A))

leftSelect0 : (x y z : ℚ) →
  (oneℚ *ℚ x) R.+ℚ (zeroℚ *ℚ y) R.+ℚ (zeroℚ *ℚ z) ≡ x
leftSelect0 x y z = solve 3 (λ a b c → (con oneℚ :* a) :+ (con zeroℚ :* b) :+ (con zeroℚ :* c) := a) refl x y z

leftSelect1 : (x y z : ℚ) →
  (zeroℚ *ℚ x) R.+ℚ (oneℚ *ℚ y) R.+ℚ (zeroℚ *ℚ z) ≡ y
leftSelect1 x y z = solve 3 (λ a b c → (con zeroℚ :* a) :+ (con oneℚ :* b) :+ (con zeroℚ :* c) := b) refl x y z

leftSelect2 : (x y z : ℚ) →
  (zeroℚ *ℚ x) R.+ℚ (zeroℚ *ℚ y) R.+ℚ (oneℚ *ℚ z) ≡ z
leftSelect2 x y z = solve 3 (λ a b c → (con zeroℚ :* a) :+ (con zeroℚ :* b) :+ (con oneℚ :* c) := c) refl x y z

rightSelect0 : (x y z : ℚ) →
  (x *ℚ oneℚ) R.+ℚ (y *ℚ zeroℚ) R.+ℚ (z *ℚ zeroℚ) ≡ x
rightSelect0 x y z = solve 3 (λ a b c → (a :* con oneℚ) :+ (b :* con zeroℚ) :+ (c :* con zeroℚ) := a) refl x y z

rightSelect1 : (x y z : ℚ) →
  (x *ℚ zeroℚ) R.+ℚ (y *ℚ oneℚ) R.+ℚ (z *ℚ zeroℚ) ≡ y
rightSelect1 x y z = solve 3 (λ a b c → (a :* con zeroℚ) :+ (b :* con oneℚ) :+ (c :* con zeroℚ) := b) refl x y z

rightSelect2 : (x y z : ℚ) →
  (x *ℚ zeroℚ) R.+ℚ (y *ℚ zeroℚ) R.+ℚ (z *ℚ oneℚ) ≡ z
rightSelect2 x y z = solve 3 (λ a b c → (a :* con zeroℚ) :+ (b :* con zeroℚ) :+ (c :* con oneℚ) := c) refl x y z

mulM-idˡ : (A : R.QMatrix3) → R.mulM R.identityM A ≡ A
mulM-idˡ A =
  qmatrix3Ext
    (leftSelect0 (R.m00 A) (R.m10 A) (R.m20 A))
    (leftSelect0 (R.m01 A) (R.m11 A) (R.m21 A))
    (leftSelect0 (R.m02 A) (R.m12 A) (R.m22 A))
    (leftSelect1 (R.m00 A) (R.m10 A) (R.m20 A))
    (leftSelect1 (R.m01 A) (R.m11 A) (R.m21 A))
    (leftSelect1 (R.m02 A) (R.m12 A) (R.m22 A))
    (leftSelect2 (R.m00 A) (R.m10 A) (R.m20 A))
    (leftSelect2 (R.m01 A) (R.m11 A) (R.m21 A))
    (leftSelect2 (R.m02 A) (R.m12 A) (R.m22 A))

mulM-idʳ : (A : R.QMatrix3) → R.mulM A R.identityM ≡ A
mulM-idʳ A =
  qmatrix3Ext
    (rightSelect0 (R.m00 A) (R.m01 A) (R.m02 A))
    (rightSelect1 (R.m00 A) (R.m01 A) (R.m02 A))
    (rightSelect2 (R.m00 A) (R.m01 A) (R.m02 A))
    (rightSelect0 (R.m10 A) (R.m11 A) (R.m12 A))
    (rightSelect1 (R.m10 A) (R.m11 A) (R.m12 A))
    (rightSelect2 (R.m10 A) (R.m11 A) (R.m12 A))
    (rightSelect0 (R.m20 A) (R.m21 A) (R.m22 A))
    (rightSelect1 (R.m20 A) (R.m21 A) (R.m22 A))
    (rightSelect2 (R.m20 A) (R.m21 A) (R.m22 A))

halfDouble : (x : ℚ) → R.halfℚ *ℚ (x R.+ℚ x) ≡ x
halfDouble x = solve 1 (λ a → con R.halfℚ :* (a :+ a) := a) refl x

halfDoubleM : (A : R.QMatrix3) → R.scaleM R.halfℚ (R.addM A A) ≡ A
halfDoubleM A =
  qmatrix3Ext
    (halfDouble (R.m00 A)) (halfDouble (R.m01 A)) (halfDouble (R.m02 A))
    (halfDouble (R.m10 A)) (halfDouble (R.m11 A)) (halfDouble (R.m12 A))
    (halfDouble (R.m20 A)) (halfDouble (R.m21 A)) (halfDouble (R.m22 A))

bulletM-comm : (A B : R.QMatrix3) → R.bulletM A B ≡ R.bulletM B A
bulletM-comm A B = cong (R.scaleM R.halfℚ) (addM-comm (R.mulM A B) (R.mulM B A))

bulletM-idˡ : (A : R.QMatrix3) → R.bulletM R.identityM A ≡ A
bulletM-idˡ A =
  trans
    (scaleM-cong-matrix R.halfℚ (addM-cong (mulM-idˡ A) (mulM-idʳ A)))
    (halfDoubleM A)

bulletM-zeroˡ : (A : R.QMatrix3) → R.bulletM R.zeroM A ≡ R.zeroM
bulletM-zeroˡ A
  rewrite mulM-zeroˡ A | mulM-zeroʳ A | addM-zeroˡ R.zeroM =
  scaleM-zero-matrix R.halfℚ

traceM-zero : R.traceM R.zeroM ≡ zeroℚ
traceM-zero = solve 0 (λ → con zeroℚ :+ con zeroℚ :+ con zeroℚ := con zeroℚ) refl

halfTimesZero : R.halfℚ *ℚ zeroℚ ≡ zeroℚ
halfTimesZero = solve 0 (λ → con R.halfℚ :* con zeroℚ := con zeroℚ) refl

crossZeroCoefficient : (x : ℚ) →
  R.halfℚ *ℚ ((zeroℚ *ℚ x) -ℚ zeroℚ) ≡ zeroℚ
crossZeroCoefficient x =
  solve 1 (λ a → con R.halfℚ :* ((con zeroℚ :* a) :- con zeroℚ) := con zeroℚ) refl x

barM-zero : R.barM R.zeroM ≡ R.zeroM
barM-zero
  rewrite traceM-zero | scaleM-zero-scalar R.identityM | subM-zero-zero =
  scaleM-zero-matrix R.halfℚ

barM-id : R.barM R.identityM ≡ R.identityM
barM-id =
  qmatrix3Ext
    (solve 0 (λ → con R.halfℚ :* (((con oneℚ :+ con oneℚ :+ con oneℚ) :* con oneℚ) :- con oneℚ) := con oneℚ) refl)
    (solve 0 (λ → con R.halfℚ :* (((con oneℚ :+ con oneℚ :+ con oneℚ) :* con zeroℚ) :- con zeroℚ) := con zeroℚ) refl)
    (solve 0 (λ → con R.halfℚ :* (((con oneℚ :+ con oneℚ :+ con oneℚ) :* con zeroℚ) :- con zeroℚ) := con zeroℚ) refl)
    (solve 0 (λ → con R.halfℚ :* (((con oneℚ :+ con oneℚ :+ con oneℚ) :* con zeroℚ) :- con zeroℚ) := con zeroℚ) refl)
    (solve 0 (λ → con R.halfℚ :* (((con oneℚ :+ con oneℚ :+ con oneℚ) :* con oneℚ) :- con oneℚ) := con oneℚ) refl)
    (solve 0 (λ → con R.halfℚ :* (((con oneℚ :+ con oneℚ :+ con oneℚ) :* con zeroℚ) :- con zeroℚ) := con zeroℚ) refl)
    (solve 0 (λ → con R.halfℚ :* (((con oneℚ :+ con oneℚ :+ con oneℚ) :* con zeroℚ) :- con zeroℚ) := con zeroℚ) refl)
    (solve 0 (λ → con R.halfℚ :* (((con oneℚ :+ con oneℚ :+ con oneℚ) :* con zeroℚ) :- con zeroℚ) := con zeroℚ) refl)
    (solve 0 (λ → con R.halfℚ :* (((con oneℚ :+ con oneℚ :+ con oneℚ) :* con oneℚ) :- con oneℚ) := con oneℚ) refl)

subSubSwapM : (X A B : R.QMatrix3) →
  R.subM (R.subM X A) B ≡ R.subM (R.subM X B) A
subSubSwapM X A B =
  qmatrix3Ext
    (solve 3 (λ x a b → (x :- a) :- b := (x :- b) :- a) refl (R.m00 X) (R.m00 A) (R.m00 B))
    (solve 3 (λ x a b → (x :- a) :- b := (x :- b) :- a) refl (R.m01 X) (R.m01 A) (R.m01 B))
    (solve 3 (λ x a b → (x :- a) :- b := (x :- b) :- a) refl (R.m02 X) (R.m02 A) (R.m02 B))
    (solve 3 (λ x a b → (x :- a) :- b := (x :- b) :- a) refl (R.m10 X) (R.m10 A) (R.m10 B))
    (solve 3 (λ x a b → (x :- a) :- b := (x :- b) :- a) refl (R.m11 X) (R.m11 A) (R.m11 B))
    (solve 3 (λ x a b → (x :- a) :- b := (x :- b) :- a) refl (R.m12 X) (R.m12 A) (R.m12 B))
    (solve 3 (λ x a b → (x :- a) :- b := (x :- b) :- a) refl (R.m20 X) (R.m20 A) (R.m20 B))
    (solve 3 (λ x a b → (x :- a) :- b := (x :- b) :- a) refl (R.m21 X) (R.m21 A) (R.m21 B))
    (solve 3 (λ x a b → (x :- a) :- b := (x :- b) :- a) refl (R.m22 X) (R.m22 A) (R.m22 B))

crossCoefficientComm : (A B : R.QMatrix3) →
  R.halfℚ *ℚ ((R.traceM A *ℚ R.traceM B) -ℚ R.traceM (R.bulletM A B))
  ≡
  R.halfℚ *ℚ ((R.traceM B *ℚ R.traceM A) -ℚ R.traceM (R.bulletM B A))
crossCoefficientComm A B
  rewrite traceM-cong (bulletM-comm A B) =
  solve 3
    (λ x y z → con R.halfℚ :* ((x :* y) :- z) := con R.halfℚ :* ((y :* x) :- z))
    refl (R.traceM A) (R.traceM B) (R.traceM (R.bulletM A B))

crossM-comm : (A B : R.QMatrix3) → R.crossM A B ≡ R.crossM B A
crossM-comm A B =
  addM-cong
    (trans
      (subSubSwapM
        (R.bulletM A B)
        (R.scaleM (R.halfℚ *ℚ R.traceM A) B)
        (R.scaleM (R.halfℚ *ℚ R.traceM B) A))
      (cong
        (λ X → R.subM
          (R.subM X (R.scaleM (R.halfℚ *ℚ R.traceM B) A))
          (R.scaleM (R.halfℚ *ℚ R.traceM A) B))
        (bulletM-comm A B)))
    (scaleM-cong-scalar (crossCoefficientComm A B) R.identityM)

crossM-zeroˡ : (A : R.QMatrix3) → R.crossM R.zeroM A ≡ R.zeroM
crossM-zeroˡ A
  rewrite bulletM-zeroˡ A
        | traceM-zero
        | halfTimesZero
        | scaleM-zero-scalar A
        | scaleM-zero-matrix (R.halfℚ *ℚ R.traceM A)
        | subM-zero-zero
        | crossZeroCoefficient (R.traceM A)
        | scaleM-zero-scalar R.identityM
        | addM-zeroˡ R.zeroM = refl

commutativeWitness : Laws.Commutative
commutativeWitness (R.rationalFirstTits27 A B C) (R.rationalFirstTits27 D E F) =
  firstTits27Ext
    (addM-cong
      (bulletM-comm A D)
      (addM-comm (R.barM (R.mulM B F)) (R.barM (R.mulM E C))))
    (addM-cong
      (addM-comm (R.mulM (R.barM A) E) (R.mulM (R.barM D) B))
      (crossM-comm C F))
    (addM-cong
      (addM-comm (R.mulM F (R.barM A)) (R.mulM C (R.barM D)))
      (crossM-comm B E))

leftUnitWitness : Laws.LeftUnit
leftUnitWitness (R.rationalFirstTits27 A B C)
  rewrite bulletM-idˡ A
        | mulM-zeroˡ C
        | mulM-zeroʳ B
        | barM-zero
        | addM-zeroˡ R.zeroM
        | addM-zeroʳ A
        | barM-id
        | mulM-idˡ B
        | mulM-zeroʳ (R.barM A)
        | crossM-zeroˡ C
        | addM-zeroʳ B
        | mulM-idʳ C
        | mulM-zeroˡ (R.barM A)
        | crossM-zeroˡ B
        | addM-zeroʳ C = refl

rightUnitWitness : Laws.RightUnit
rightUnitWitness X =
  trans (commutativeWitness X R.unitJ) (leftUnitWitness X)

cubicUnitWitness : Laws.CubicUnit
cubicUnitWitness =
  solve 0
    (λ →
      (((con oneℚ :* con oneℚ) :* con oneℚ)
       :+ ((con zeroℚ :* con zeroℚ) :* con zeroℚ)
       :+ ((con zeroℚ :* con zeroℚ) :* con zeroℚ)
       :- ((con zeroℚ :* con oneℚ) :* con zeroℚ)
       :- ((con zeroℚ :* con zeroℚ) :* con oneℚ)
       :- ((con oneℚ :* con zeroℚ) :* con zeroℚ)
       :+ con zeroℚ
       :+ con zeroℚ
       :- con zeroℚ)
      := con oneℚ)
    refl

record BasicRationalFirstTitsLawWitnesses : Set where
  constructor basic-rational-first-tits-law-witnesses
  field
    commutative : Laws.Commutative
    leftUnit : Laws.LeftUnit
    rightUnit : Laws.RightUnit
    cubicUnit : Laws.CubicUnit
open BasicRationalFirstTitsLawWitnesses public

canonicalBasicRationalFirstTitsLawWitnesses : BasicRationalFirstTitsLawWitnesses
canonicalBasicRationalFirstTitsLawWitnesses =
  basic-rational-first-tits-law-witnesses
    commutativeWitness leftUnitWitness rightUnitWitness cubicUnitWitness

record BasicLawBoundary : Set where
  constructor basic-law-boundary
  field
    rationalSolverReused : Bool
    commutativityProofTermSourceWritten : Bool
    twoSidedUnitProofTermsSourceWritten : Bool
    cubicUnitProofTermSourceWritten : Bool
    bilinearityProofTermsSourceWritten : Bool
    cubicHomogeneityProofTermSourceWritten : Bool
    jordanIdentityProofTermSourceWritten : Bool
    fullPaidLawPackageInhabited : Bool
    exactHeadAgdaKernelReceiptPresent : Bool
    externalAlbertClassificationUsedForTheseWitnesses : Bool
    boundary : String
open BasicLawBoundary public

canonicalBasicLawBoundary : BasicLawBoundary
canonicalBasicLawBoundary =
  basic-law-boundary
    true true true true false false false false false false
    "This owner source-writes literal terms for product commutativity, two-sided unit and cubic(unit)=1 using the repository's existing Data.Rational.Solver route on the exact M3(Q)^3 definitions. Matrix identity/zero, bar(1)=1, bar(0)=0 and cross(0,A)=0 are paid internally rather than borrowed from external Albert classification. Bilinearity, cubic homogeneity, Jordan identity and the full PaidRationalFirstTitsLaws package remain open. No exact-head Agda kernel receipt is claimed in this runtime."
