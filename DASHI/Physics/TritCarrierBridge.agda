module DASHI.Physics.TritCarrierBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_∸_)
open import Data.Vec using (Vec; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (cong)

open import Base369 using (TriTruth; rotateTri)
open import DASHI.Algebra.TritTriTruthBridge using
  ( toTriTruth
  ; fromTriTruth
  ; rotTrit
  ; toFrom
  ; fromTo
  ; rotTrit-equivariant-to
  )
open import DASHI.Algebra.Trit using (neg; zer; pos; inv)
import DASHI.Metric.AgreementUltrametric as AU
import DASHI.Physics.RealTernaryCarrier as RTC

TriTruthCarrier : Nat → Set
TriTruthCarrier n = Vec TriTruth n

liftToTriTruth : ∀ {n} → RTC.Carrier n → TriTruthCarrier n
liftToTriTruth = map toTriTruth

liftFromTriTruth : ∀ {n} → TriTruthCarrier n → RTC.Carrier n
liftFromTriTruth = map fromTriTruth

liftToFrom :
  ∀ {n} (xs : TriTruthCarrier n) →
  liftToTriTruth (liftFromTriTruth xs) ≡ xs
liftToFrom [] = refl
liftToFrom (x ∷ xs) rewrite toFrom x | liftToFrom xs = refl

liftFromTo :
  ∀ {n} (xs : RTC.Carrier n) →
  liftFromTriTruth (liftToTriTruth xs) ≡ xs
liftFromTo [] = refl
liftFromTo (x ∷ xs) rewrite fromTo x | liftFromTo xs = refl

rotate-lift-equivariant :
  ∀ {n} (xs : RTC.Carrier n) →
  liftToTriTruth (map rotTrit xs) ≡ map rotateTri (liftToTriTruth xs)
rotate-lift-equivariant [] = refl
rotate-lift-equivariant (x ∷ xs)
  rewrite rotTrit-equivariant-to x
        | rotate-lift-equivariant xs = refl

agreeDepth-rotTrit :
  ∀ {n} (x y : RTC.Carrier n) →
  AU.agreeDepth (map rotTrit x) (map rotTrit y) ≡ AU.agreeDepth x y
agreeDepth-rotTrit [] [] = refl
agreeDepth-rotTrit (neg ∷ xs) (neg ∷ ys)
  rewrite agreeDepth-rotTrit xs ys = refl
agreeDepth-rotTrit (neg ∷ xs) (zer ∷ ys) = refl
agreeDepth-rotTrit (neg ∷ xs) (pos ∷ ys) = refl
agreeDepth-rotTrit (zer ∷ xs) (neg ∷ ys) = refl
agreeDepth-rotTrit (zer ∷ xs) (zer ∷ ys)
  rewrite agreeDepth-rotTrit xs ys = refl
agreeDepth-rotTrit (zer ∷ xs) (pos ∷ ys) = refl
agreeDepth-rotTrit (pos ∷ xs) (neg ∷ ys) = refl
agreeDepth-rotTrit (pos ∷ xs) (zer ∷ ys) = refl
agreeDepth-rotTrit (pos ∷ xs) (pos ∷ ys)
  rewrite agreeDepth-rotTrit xs ys = refl

dNat-rotTrit :
  ∀ {n} (x y : RTC.Carrier n) →
  AU.dNat (map rotTrit x) (map rotTrit y) ≡ AU.dNat x y
dNat-rotTrit {n} x y =
  cong (λ k → n ∸ k) (agreeDepth-rotTrit x y)

dNat-reflection :
  ∀ {n} (x y : RTC.Carrier n) →
  AU.dNat (map inv x) (map inv y) ≡ AU.dNat x y
dNat-reflection = AU.dNat-inv

record TritCarrierBridge (n : Nat) : Set where
  constructor tritCarrierBridge
  field
    toCarrier : RTC.Carrier n → TriTruthCarrier n
    fromCarrier : TriTruthCarrier n → RTC.Carrier n
    toFromCarrier :
      ∀ xs → toCarrier (fromCarrier xs) ≡ xs
    fromToCarrier :
      ∀ xs → fromCarrier (toCarrier xs) ≡ xs
    rotationLift :
      ∀ xs → toCarrier (map rotTrit xs) ≡ map rotateTri (toCarrier xs)
    rotationIsometry :
      (x y : RTC.Carrier n) →
      AU.dNat (map rotTrit x) (map rotTrit y) ≡ AU.dNat x y
    reflectionIsometry :
      (x y : RTC.Carrier n) →
      AU.dNat (map inv x) (map inv y) ≡ AU.dNat x y

tritCarrierBridgeSurface : ∀ n → TritCarrierBridge n
tritCarrierBridgeSurface n =
  tritCarrierBridge
    liftToTriTruth
    liftFromTriTruth
    liftToFrom
    liftFromTo
    rotate-lift-equivariant
    (λ x y → dNat-rotTrit x y)
    (λ x y → dNat-reflection x y)
