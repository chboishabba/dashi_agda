module DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsUnitWitnessExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (trans)
open import Data.Rational.Solver using (module +-*-Solver)

open +-*-Solver using (solve; _:+_; _:-_; _:*_; con; _:=_)
open import DASHI.Core.Q using (ℚ; _+ℚ_; _-ℚ_; _*ℚ_; zeroℚ; oneℚ)
import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsCarrierExact as R
import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsLawObligationsExact as Laws
import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsBasicLawWitnessesExact as Basic

------------------------------------------------------------------------
-- TWO-SIDED UNIT FOR THE LITERAL RATIONAL FIRST-TITS PRODUCT
--
-- The proof reduces the three product blocks using only explicit matrix
-- identities over Q:
--
--   I A = A, A I = A, 0 A = A 0 = 0,
--   I bullet A = A,
--   bar(I)=I, bar(0)=0,
--   0 cross A = 0.
--
-- Left unit is then literal block reduction for unitJ=(I,0,0). Right unit is
-- derived from the separately source-written commutativity witness. No Albert
-- classification theorem is used.
--
-- This is SOURCE-WRITTEN. Without an exact-head Agda run it is not represented
-- as a kernel-green receipt.
------------------------------------------------------------------------

scaleM-cong-matrix :
  (q : ℚ) → {A B : R.QMatrix3} → A ≡ B → R.scaleM q A ≡ R.scaleM q B
scaleM-cong-matrix q refl = refl

addM-zeroˡ : (A : R.QMatrix3) → R.addM R.zeroM A ≡ A
addM-zeroˡ A =
  Basic.qmatrix3Ext
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
addM-zeroʳ A = trans (Basic.addM-comm A R.zeroM) (addM-zeroˡ A)

subM-zero-zero : R.subM R.zeroM R.zeroM ≡ R.zeroM
subM-zero-zero =
  Basic.qmatrix3Ext
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
  Basic.qmatrix3Ext
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
  Basic.qmatrix3Ext
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
  (zeroℚ *ℚ x) +ℚ (zeroℚ *ℚ y) +ℚ (zeroℚ *ℚ z) ≡ zeroℚ
zeroDotLeft x y z =
  solve 3
    (λ a b c → (con zeroℚ :* a) :+ (con zeroℚ :* b) :+ (con zeroℚ :* c) := con zeroℚ)
    refl x y z

zeroDotRight : (x y z : ℚ) →
  (x *ℚ zeroℚ) +ℚ (y *ℚ zeroℚ) +ℚ (z *ℚ zeroℚ) ≡ zeroℚ
zeroDotRight x y z =
  solve 3
    (λ a b c → (a :* con zeroℚ) :+ (b :* con zeroℚ) :+ (c :* con zeroℚ) := con zeroℚ)
    refl x y z

mulM-zeroˡ : (A : R.QMatrix3) → R.mulM R.zeroM A ≡ R.zeroM
mulM-zeroˡ A =
  Basic.qmatrix3Ext
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
  Basic.qmatrix3Ext
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
  (oneℚ *ℚ x) +ℚ (zeroℚ *ℚ y) +ℚ (zeroℚ *ℚ z) ≡ x
leftSelect0 x y z = solve 3 (λ a b c → (con oneℚ :* a) :+ (con zeroℚ :* b) :+ (con zeroℚ :* c) := a) refl x y z

leftSelect1 : (x y z : ℚ) →
  (zeroℚ *ℚ x) +ℚ (oneℚ *ℚ y) +ℚ (zeroℚ *ℚ z) ≡ y
leftSelect1 x y z = solve 3 (λ a b c → (con zeroℚ :* a) :+ (con oneℚ :* b) :+ (con zeroℚ :* c) := b) refl x y z

leftSelect2 : (x y z : ℚ) →
  (zeroℚ *ℚ x) +ℚ (zeroℚ *ℚ y) +ℚ (oneℚ *ℚ z) ≡ z
leftSelect2 x y z = solve 3 (λ a b c → (con zeroℚ :* a) :+ (con zeroℚ :* b) :+ (con oneℚ :* c) := c) refl x y z

rightSelect0 : (x y z : ℚ) →
  (x *ℚ oneℚ) +ℚ (y *ℚ zeroℚ) +ℚ (z *ℚ zeroℚ) ≡ x
rightSelect0 x y z = solve 3 (λ a b c → (a :* con oneℚ) :+ (b :* con zeroℚ) :+ (c :* con zeroℚ) := a) refl x y z

rightSelect1 : (x y z : ℚ) →
  (x *ℚ zeroℚ) +ℚ (y *ℚ oneℚ) +ℚ (z *ℚ zeroℚ) ≡ y
rightSelect1 x y z = solve 3 (λ a b c → (a :* con zeroℚ) :+ (b :* con oneℚ) :+ (c :* con zeroℚ) := b) refl x y z

rightSelect2 : (x y z : ℚ) →
  (x *ℚ zeroℚ) +ℚ (y *ℚ zeroℚ) +ℚ (z *ℚ oneℚ) ≡ z
rightSelect2 x y z = solve 3 (λ a b c → (a :* con zeroℚ) :+ (b :* con zeroℚ) :+ (c :* con oneℚ) := c) refl x y z

mulM-idˡ : (A : R.QMatrix3) → R.mulM R.identityM A ≡ A
mulM-idˡ A =
  Basic.qmatrix3Ext
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
  Basic.qmatrix3Ext
    (rightSelect0 (R.m00 A) (R.m01 A) (R.m02 A))
    (rightSelect1 (R.m00 A) (R.m01 A) (R.m02 A))
    (rightSelect2 (R.m00 A) (R.m01 A) (R.m02 A))
    (rightSelect0 (R.m10 A) (R.m11 A) (R.m12 A))
    (rightSelect1 (R.m10 A) (R.m11 A) (R.m12 A))
    (rightSelect2 (R.m10 A) (R.m11 A) (R.m12 A))
    (rightSelect0 (R.m20 A) (R.m21 A) (R.m22 A))
    (rightSelect1 (R.m20 A) (R.m21 A) (R.m22 A))
    (rightSelect2 (R.m20 A) (R.m21 A) (R.m22 A))

halfDouble : (x : ℚ) → R.halfℚ *ℚ (x +ℚ x) ≡ x
halfDouble x = solve 1 (λ a → con R.halfℚ :* (a :+ a) := a) refl x

halfDoubleM : (A : R.QMatrix3) → R.scaleM R.halfℚ (R.addM A A) ≡ A
halfDoubleM A =
  Basic.qmatrix3Ext
    (halfDouble (R.m00 A)) (halfDouble (R.m01 A)) (halfDouble (R.m02 A))
    (halfDouble (R.m10 A)) (halfDouble (R.m11 A)) (halfDouble (R.m12 A))
    (halfDouble (R.m20 A)) (halfDouble (R.m21 A)) (halfDouble (R.m22 A))

bulletM-idˡ : (A : R.QMatrix3) → R.bulletM R.identityM A ≡ A
bulletM-idˡ A =
  trans
    (scaleM-cong-matrix R.halfℚ (Basic.addM-cong (mulM-idˡ A) (mulM-idʳ A)))
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
  Basic.qmatrix3Ext
    (solve 0 (λ → con R.halfℚ :* (((con oneℚ :+ con oneℚ :+ con oneℚ) :* con oneℚ) :- con oneℚ) := con oneℚ) refl)
    (solve 0 (λ → con R.halfℚ :* (((con oneℚ :+ con oneℚ :+ con oneℚ) :* con zeroℚ) :- con zeroℚ) := con zeroℚ) refl)
    (solve 0 (λ → con R.halfℚ :* (((con oneℚ :+ con oneℚ :+ con oneℚ) :* con zeroℚ) :- con zeroℚ) := con zeroℚ) refl)
    (solve 0 (λ → con R.halfℚ :* (((con oneℚ :+ con oneℚ :+ con oneℚ) :* con zeroℚ) :- con zeroℚ) := con zeroℚ) refl)
    (solve 0 (λ → con R.halfℚ :* (((con oneℚ :+ con oneℚ :+ con oneℚ) :* con oneℚ) :- con oneℚ) := con oneℚ) refl)
    (solve 0 (λ → con R.halfℚ :* (((con oneℚ :+ con oneℚ :+ con oneℚ) :* con zeroℚ) :- con zeroℚ) := con zeroℚ) refl)
    (solve 0 (λ → con R.halfℚ :* (((con oneℚ :+ con oneℚ :+ con oneℚ) :* con zeroℚ) :- con zeroℚ) := con zeroℚ) refl)
    (solve 0 (λ → con R.halfℚ :* (((con oneℚ :+ con oneℚ :+ con oneℚ) :* con zeroℚ) :- con zeroℚ) := con zeroℚ) refl)
    (solve 0 (λ → con R.halfℚ :* (((con oneℚ :+ con oneℚ :+ con oneℚ) :* con oneℚ) :- con oneℚ) := con oneℚ) refl)

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
  trans (Basic.commutativeWitness X R.unitJ) (leftUnitWitness X)

record RationalFirstTitsUnitWitnesses : Set where
  constructor rational-first-tits-unit-witnesses
  field
    leftUnit : Laws.LeftUnit
    rightUnit : Laws.RightUnit
open RationalFirstTitsUnitWitnesses public

canonicalRationalFirstTitsUnitWitnesses : RationalFirstTitsUnitWitnesses
canonicalRationalFirstTitsUnitWitnesses =
  rational-first-tits-unit-witnesses leftUnitWitness rightUnitWitness

record UnitBoundary : Set where
  constructor unit-boundary
  field
    matrixIdentityAndZeroTermsSourceWritten : Bool
    barIdentityAndZeroTermsSourceWritten : Bool
    crossZeroTermSourceWritten : Bool
    leftUnitProofTermSourceWritten : Bool
    rightUnitProofTermSourceWritten : Bool
    externalAlbertClassificationUsed : Bool
    exactHeadAgdaKernelReceiptPresent : Bool
    boundary : String
open UnitBoundary public

canonicalUnitBoundary : UnitBoundary
canonicalUnitBoundary =
  unit-boundary
    true true true true true false false
    "Two-sided unit is source-written from literal QMatrix3 identities plus the existing rational solver and basic commutativity witness. It does not use external Albert classification. Because this runtime has no Agda executable, the proof terms remain kernel-unverified until an exact-head typecheck receipt exists."
