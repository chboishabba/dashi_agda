module DASHI.Physics.QuadraticPolarization where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import Data.Vec using (Vec; []; _∷_; map; zipWith)
open import Data.Product using (_×_; _,_)

open import Data.Integer using (ℤ; _+_; _-_; _*_; -_; +_; -[1+_])
open import Data.Integer.Properties as IntP
import Relation.Binary.Reasoning.Setoid as EqR
open import Data.Nat using (_≤_; _<_)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

module ℤ-Reasoning = EqR IntP.≡-setoid
open ℤ-Reasoning

------------------------------------------------------------------------
-- Trit → ℤ embedding (for polarization we want ℤ, not Trit)

intOfTrit : Trit → ℤ
intOfTrit neg = -[1+ 0 ]   -- -1
intOfTrit zer = + 0
intOfTrit pos = + 1

vecℤ : ∀ {m : Nat} → Vec Trit m → Vec ℤ m
vecℤ = map intOfTrit

------------------------------------------------------------------------
-- ℤ vector ops

_+ᵥ_ : ∀ {m : Nat} → Vec ℤ m → Vec ℤ m → Vec ℤ m
_+ᵥ_ = zipWith _+_

dotℤ : ∀ {m : Nat} → Vec ℤ m → Vec ℤ m → ℤ
dotℤ []       []       = + 0
dotℤ (x ∷ xs) (y ∷ ys) = (x * y) + dotℤ xs ys

sumℤ : ∀ {m : Nat} → Vec ℤ m → ℤ
sumℤ []       = + 0
sumℤ (x ∷ xs) = x + sumℤ xs

replicateTrit0 : (m : Nat) → Vec Trit m
replicateTrit0 zero    = []
replicateTrit0 (suc n) = zer ∷ replicateTrit0 n

zeroVecℤ : ∀ {m : Nat} → Vec ℤ m
zeroVecℤ {zero} = []
zeroVecℤ {suc m} = + 0 ∷ zeroVecℤ {m}

vecℤ-replicateTrit0 :
  ∀ {m : Nat} → vecℤ (replicateTrit0 m) ≡ zeroVecℤ {m}
vecℤ-replicateTrit0 {zero} = refl
vecℤ-replicateTrit0 {suc m} = cong (λ t → (+ 0) ∷ t) (vecℤ-replicateTrit0 {m})

zeroVecℤ+ᵥ :
  ∀ {m : Nat} (v : Vec ℤ m) → zeroVecℤ {m} +ᵥ v ≡ v
zeroVecℤ+ᵥ {zero} [] = refl
zeroVecℤ+ᵥ {suc m} (x ∷ xs) =
  cong₂ _∷_ (IntP.+-identityˡ x) (zeroVecℤ+ᵥ {m} xs)

------------------------------------------------------------------------
-- Quadratic form on core: sum of squares in ℤ

Qcoreℤ : ∀ {m : Nat} → Vec Trit m → ℤ
Qcoreℤ {m} x =
  let v = vecℤ x in
  sumℤ (map (λ z → z * z) v)

------------------------------------------------------------------------
-- Correct polarization over the ℤ-embedding:
-- B₂ℤ(Q)(x,y) = Q̂(v(x)+v(y)) - Q̂(v(x)) - Q̂(v(y))
-- where Q̂ is a quadratic on Vec ℤ m.

Q̂core : ∀ {m : Nat} → Vec ℤ m → ℤ
Q̂core v = sumℤ (map (λ z → z * z) v)

B₂ℤ : ∀ {m : Nat}
    → (Q̂ : Vec ℤ m → ℤ)
    → Vec Trit m → Vec Trit m → ℤ
B₂ℤ Q̂ x y =
  (Q̂ (vecℤ x +ᵥ vecℤ y)) - (Q̂ (vecℤ x)) - (Q̂ (vecℤ y))

------------------------------------------------------------------------
-- Helpers for constructive polarization

-- Scalar polarization identity, specialized to trits.
-- We prove by case split over (neg/zer/pos) × (neg/zer/pos);
-- all goals reduce by computation.

b2-trit :
  (a b : Trit) →
  (intOfTrit a + intOfTrit b) * (intOfTrit a + intOfTrit b)
    - (intOfTrit a * intOfTrit a)
    - (intOfTrit b * intOfTrit b)
    ≡ (+ 2) * (intOfTrit a * intOfTrit b)
b2-trit neg neg = refl
b2-trit neg zer = refl
b2-trit neg pos = refl
b2-trit zer neg = refl
b2-trit zer zer = refl
b2-trit zer pos = refl
b2-trit pos neg = refl
b2-trit pos zer = refl
b2-trit pos pos = refl

postulate
  split-B₂ :
    (A R X RX Y RY : ℤ) →
    (A + R) - (X + RX) - (Y + RY) ≡ (A - X - Y) + (R - RX - RY)
------------------------------------------------------------------------
-- Sanity property for Q̂core (constructive)

Q̂core-zero :
  ∀ {m : Nat} → Q̂core (vecℤ (replicateTrit0 m)) ≡ + 0
Q̂core-zero {zero} = refl
Q̂core-zero {suc m} =
  cong (λ n → (+ 0 * + 0) + n) (Q̂core-zero {m})

B₂ℤ-zeroL :
  ∀ {m : Nat} (x : Vec Trit m) →
  B₂ℤ Q̂core (replicateTrit0 m) x ≡ + 0
B₂ℤ-zeroL {m} x =
  begin
    B₂ℤ Q̂core (replicateTrit0 m) x
  ≡⟨ refl ⟩
    (Q̂core (vecℤ (replicateTrit0 m) +ᵥ vecℤ x)) - (Q̂core (vecℤ (replicateTrit0 m))) - (Q̂core (vecℤ x))
  ≡⟨ cong (λ v → Q̂core v - Q̂core (vecℤ (replicateTrit0 m)) - Q̂core (vecℤ x))
        (trans (cong (λ t → t +ᵥ vecℤ x) (vecℤ-replicateTrit0 {m}))
               (zeroVecℤ+ᵥ (vecℤ x))) ⟩
    (Q̂core (vecℤ x)) - (Q̂core (vecℤ (replicateTrit0 m))) - (Q̂core (vecℤ x))
  ≡⟨ cong (λ z → Q̂core (vecℤ x) - z - Q̂core (vecℤ x))
        (Q̂core-zero {m}) ⟩
    (Q̂core (vecℤ x)) - (+ 0) - (Q̂core (vecℤ x))
  ≡⟨ refl ⟩
    (Q̂core (vecℤ x) + (- (+ 0))) + (- Q̂core (vecℤ x))
  ≡⟨ cong (λ t → Q̂core (vecℤ x) + t + (- Q̂core (vecℤ x)))
        (refl) ⟩
    (Q̂core (vecℤ x) + (+ 0)) + (- Q̂core (vecℤ x))
  ≡⟨ cong (λ t → t + (- Q̂core (vecℤ x)))
        (IntP.+-identityʳ (Q̂core (vecℤ x))) ⟩
    (Q̂core (vecℤ x)) + (- Q̂core (vecℤ x))
  ≡⟨ IntP.+-inverseʳ (Q̂core (vecℤ x)) ⟩
    + 0
  ∎

------------------------------------------------------------------------
-- Main target theorem to chase:
-- For Q̂core(v)=∑ vᵢ² we should have:
--   B₂ℤ Q̂core x y = 2 * dotℤ (vecℤ x) (vecℤ y)

B₂ℤ-Q̂core-dot2 :
  ∀ {m : Nat} (x y : Vec Trit m) →
  B₂ℤ Q̂core x y ≡ ((+ 2) * dotℤ (vecℤ x) (vecℤ y))
B₂ℤ-Q̂core-dot2 [] [] =
  begin
    B₂ℤ Q̂core [] []
  ≡⟨ refl ⟩
    + 0
  ≡⟨ sym (IntP.*-zeroʳ (+ 2)) ⟩
    (+ 2) * (+ 0)
  ∎
B₂ℤ-Q̂core-dot2 (x ∷ xs) (y ∷ ys) =
  begin
    B₂ℤ Q̂core (x ∷ xs) (y ∷ ys)
  ≡⟨ refl ⟩
    (Q̂core ((vecℤ (x ∷ xs)) +ᵥ (vecℤ (y ∷ ys))))
      - (Q̂core (vecℤ (x ∷ xs)))
      - (Q̂core (vecℤ (y ∷ ys)))
  ≡⟨ refl ⟩
    ((intOfTrit x + intOfTrit y) * (intOfTrit x + intOfTrit y)
      + Q̂core (vecℤ xs +ᵥ vecℤ ys))
      - ((intOfTrit x * intOfTrit x) + Q̂core (vecℤ xs))
      - ((intOfTrit y * intOfTrit y) + Q̂core (vecℤ ys))
  ≡⟨ split-B₂
        ((intOfTrit x + intOfTrit y) * (intOfTrit x + intOfTrit y))
        (Q̂core (vecℤ xs +ᵥ vecℤ ys))
        (intOfTrit x * intOfTrit x)
        (Q̂core (vecℤ xs))
        (intOfTrit y * intOfTrit y)
        (Q̂core (vecℤ ys)) ⟩
    ((intOfTrit x + intOfTrit y) * (intOfTrit x + intOfTrit y)
      - (intOfTrit x * intOfTrit x)
      - (intOfTrit y * intOfTrit y))
      + (Q̂core (vecℤ xs +ᵥ vecℤ ys) - Q̂core (vecℤ xs) - Q̂core (vecℤ ys))
  ≡⟨ cong (λ t → t + (B₂ℤ Q̂core xs ys)) (b2-trit x y) ⟩
    ((+ 2) * (intOfTrit x * intOfTrit y)) + (B₂ℤ Q̂core xs ys)
  ≡⟨ cong (λ t → ((+ 2) * (intOfTrit x * intOfTrit y)) + t) (B₂ℤ-Q̂core-dot2 xs ys) ⟩
    ((+ 2) * (intOfTrit x * intOfTrit y)) + ((+ 2) * dotℤ (vecℤ xs) (vecℤ ys))
  ≡⟨ sym (IntP.*-distribˡ-+ (+ 2) (intOfTrit x * intOfTrit y) (dotℤ (vecℤ xs) (vecℤ ys))) ⟩
    (+ 2) * ((intOfTrit x * intOfTrit y) + dotℤ (vecℤ xs) (vecℤ ys))
  ∎
  where
    open ℤ-Reasoning
