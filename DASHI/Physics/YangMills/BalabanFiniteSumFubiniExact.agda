module DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; _+_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (Product; pair; cartesian)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational; sumRationalCong)

------------------------------------------------------------------------
-- Exact finite-sum Fubini calculus.
------------------------------------------------------------------------

sumRationalZero : ∀ {A : Set} (values : List A) →
  sumRational values (λ _ → 0ℚ) ≡ 0ℚ
sumRationalZero [] = refl
sumRationalZero (value ∷ values)
  rewrite sumRationalZero values = ℚRing.solve-∀

sumRationalAdd :
  ∀ {A : Set} (values : List A) (left right : A → ℚ) →
  sumRational values (λ value → left value + right value)
  ≡ sumRational values left + sumRational values right
sumRationalAdd [] left right = ℚRing.solve-∀
sumRationalAdd (value ∷ values) left right
  rewrite sumRationalAdd values left right =
  ℚRing.solve-∀
    (left value) (right value)
    (sumRational values left) (sumRational values right)

sumRationalAppend :
  ∀ {A : Set} (left right : List A) (term : A → ℚ) →
  sumRational (left ++ right) term
  ≡ sumRational left term + sumRational right term
sumRationalAppend [] right term = ℚRing.solve-∀ (sumRational right term)
sumRationalAppend (value ∷ left) right term
  rewrite sumRationalAppend left right term =
  ℚRing.solve-∀
    (term value) (sumRational left term) (sumRational right term)

sumRationalMap :
  ∀ {A B : Set} (mapValue : A → B) (values : List A) (term : B → ℚ) →
  sumRational (map mapValue values) term
  ≡ sumRational values (λ value → term (mapValue value))
sumRationalMap mapValue [] term = refl
sumRationalMap mapValue (value ∷ values) term
  rewrite sumRationalMap mapValue values term = refl

sumCartesian :
  ∀ {A B : Set} (left : List A) (right : List B)
    (term : Product A B → ℚ) →
  sumRational (cartesian left right) term
  ≡ sumRational left
      (λ leftValue →
        sumRational right
          (λ rightValue → term (pair leftValue rightValue)))
sumCartesian [] right term = refl
sumCartesian (leftValue ∷ left) right term =
  trans
    (sumRationalAppend
      (map (λ rightValue → pair leftValue rightValue) right)
      (cartesian left right)
      term)
    (trans
      (cong₂ _+_
        (sumRationalMap
          (λ rightValue → pair leftValue rightValue)
          right term)
        (sumCartesian left right term))
      refl)

sumSwap :
  ∀ {A B : Set} (left : List A) (right : List B)
    (term : A → B → ℚ) →
  sumRational left (λ leftValue → sumRational right (term leftValue))
  ≡ sumRational right
      (λ rightValue → sumRational left (λ leftValue → term leftValue rightValue))
sumSwap [] right term = sym (sumRationalZero right)
sumSwap (leftValue ∷ left) right term =
  trans
    (cong₂ _+_ refl (sumSwap left right term))
    (sym
      (sumRationalAdd right
        (term leftValue)
        (λ rightValue →
          sumRational left (λ leftItem → term leftItem rightValue))))

------------------------------------------------------------------------
-- Four-axis sum order and the three rotations used by physical fibres.
------------------------------------------------------------------------

sum4 :
  ∀ {A0 A1 A2 A3 : Set} →
  List A0 → List A1 → List A2 → List A3 →
  (A0 → A1 → A2 → A3 → ℚ) → ℚ
sum4 axis0 axis1 axis2 axis3 term =
  sumRational axis0 (λ x0 →
    sumRational axis1 (λ x1 →
      sumRational axis2 (λ x2 →
        sumRational axis3 (term x0 x1 x2))))

rotateAxis2ToCanonical :
  ∀ {A0 A1 A2 A3 : Set}
    (axis0 : List A0) (axis1 : List A1)
    (axis2 : List A2) (axis3 : List A3)
    (term : A0 → A1 → A2 → A3 → ℚ) →
  sumRational axis0 (λ x0 →
    sumRational axis1 (λ x1 →
      sumRational axis3 (λ x3 →
        sumRational axis2 (λ x2 → term x0 x1 x2 x3))))
  ≡ sum4 axis0 axis1 axis2 axis3 term
rotateAxis2ToCanonical axis0 axis1 axis2 axis3 term =
  sumRationalCong axis0 _ _ (λ x0 →
    sumRationalCong axis1 _ _ (λ x1 →
      sumSwap axis3 axis2 (λ x3 x2 → term x0 x1 x2 x3)))

rotateAxis1ToCanonical :
  ∀ {A0 A1 A2 A3 : Set}
    (axis0 : List A0) (axis1 : List A1)
    (axis2 : List A2) (axis3 : List A3)
    (term : A0 → A1 → A2 → A3 → ℚ) →
  sumRational axis0 (λ x0 →
    sumRational axis2 (λ x2 →
      sumRational axis3 (λ x3 →
        sumRational axis1 (λ x1 → term x0 x1 x2 x3))))
  ≡ sum4 axis0 axis1 axis2 axis3 term
rotateAxis1ToCanonical axis0 axis1 axis2 axis3 term =
  trans
    (sumRationalCong axis0 _ _ (λ x0 →
      sumRationalCong axis2 _ _ (λ x2 →
        sumSwap axis3 axis1 (λ x3 x1 → term x0 x1 x2 x3))))
    (sumRationalCong axis0 _ _ (λ x0 →
      sumSwap axis2 axis1 (λ x2 x1 →
        sumRational axis3 (λ x3 → term x0 x1 x2 x3))))

rotateAxis0ToCanonical :
  ∀ {A0 A1 A2 A3 : Set}
    (axis0 : List A0) (axis1 : List A1)
    (axis2 : List A2) (axis3 : List A3)
    (term : A0 → A1 → A2 → A3 → ℚ) →
  sumRational axis1 (λ x1 →
    sumRational axis2 (λ x2 →
      sumRational axis3 (λ x3 →
        sumRational axis0 (λ x0 → term x0 x1 x2 x3))))
  ≡ sum4 axis0 axis1 axis2 axis3 term
rotateAxis0ToCanonical axis0 axis1 axis2 axis3 term =
  trans
    (sumRationalCong axis1 _ _ (λ x1 →
      sumRationalCong axis2 _ _ (λ x2 →
        sumSwap axis3 axis0 (λ x3 x0 → term x0 x1 x2 x3))))
    (trans
      (sumRationalCong axis1 _ _ (λ x1 →
        sumSwap axis2 axis0 (λ x2 x0 →
          sumRational axis3 (λ x3 → term x0 x1 x2 x3))))
      (sumSwap axis1 axis0 (λ x1 x0 →
        sumRational axis2 (λ x2 →
          sumRational axis3 (λ x3 → term x0 x1 x2 x3)))))

finiteSumAppendLevel : ProofLevel
finiteSumAppendLevel = machineChecked

finiteCartesianFubiniLevel : ProofLevel
finiteCartesianFubiniLevel = machineChecked

finiteSumSwapLevel : ProofLevel
finiteSumSwapLevel = machineChecked

fourAxisSumRotationLevel : ProofLevel
fourAxisSumRotationLevel = machineChecked
