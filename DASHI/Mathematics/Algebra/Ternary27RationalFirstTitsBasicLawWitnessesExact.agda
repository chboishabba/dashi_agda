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
-- SMALL PROOF-RELEVANT SLICE FOR THE LITERAL RATIONAL FIRST-TITS CARRIER.
--
-- Source-written here, using only the repo's rational solver:
--   * product commutativity;
--   * cubic(unit)=1.
--
-- The longer unit derivation is kept in a separate owner so this basic slice
-- remains easy to audit. No kernel-green claim is made without Agda execution.
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

bulletM-comm : (A B : R.QMatrix3) → R.bulletM A B ≡ R.bulletM B A
bulletM-comm A B = cong (R.scaleM R.halfℚ) (addM-comm (R.mulM A B) (R.mulM B A))

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
    cubicUnit : Laws.CubicUnit
open BasicRationalFirstTitsLawWitnesses public

canonicalBasicRationalFirstTitsLawWitnesses : BasicRationalFirstTitsLawWitnesses
canonicalBasicRationalFirstTitsLawWitnesses =
  basic-rational-first-tits-law-witnesses commutativeWitness cubicUnitWitness

record BasicLawBoundary : Set where
  constructor basic-law-boundary
  field
    rationalSolverReused : Bool
    commutativityProofTermSourceWritten : Bool
    cubicUnitProofTermSourceWritten : Bool
    fullPaidLawPackageInhabited : Bool
    exactHeadAgdaKernelReceiptPresent : Bool
    externalAlbertClassificationUsedForTheseWitnesses : Bool
    boundary : String
open BasicLawBoundary public

canonicalBasicLawBoundary : BasicLawBoundary
canonicalBasicLawBoundary =
  basic-law-boundary
    true true true false false false
    "This minimal owner source-writes literal commutativity and cubic(unit)=1 proof terms using the repository's rational solver and exact M3(Q)^3 definitions. Longer unit/bilinearity/Jordan obligations live in separate proof-relevant owners. No exact-head Agda kernel receipt or external-classification substitution is claimed."
