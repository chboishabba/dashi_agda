module DASHI.Physics.IndefiniteMaskQuadratic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import Data.Vec using (Vec; []; _∷_; zipWith)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Data.Integer using (ℤ; _+_; _-_; _*_; -_; +_; -[1+_])
open import Data.Integer.Properties as IntP
import Relation.Binary.Reasoning.Setoid as EqR

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

module ℤ-Reasoning = EqR IntP.≡-setoid
open ℤ-Reasoning

------------------------------------------------------------------------
-- Sign mask

data Sign : Set where
  plus  : Sign
  minus : Sign

signℤ : Sign → ℤ
signℤ plus  = + 1
signℤ minus = -[1+ 0 ]   -- -1

------------------------------------------------------------------------
-- Trit → ℤ

toℤTrit : Trit → ℤ
toℤTrit neg = -[1+ 0 ]   -- -1
toℤTrit zer = + 0
toℤTrit pos = + 1

sqℤ : ℤ → ℤ
sqℤ x = x * x

------------------------------------------------------------------------
-- Sum on Vec ℤ

sumℤ : ∀ {m : Nat} → Vec ℤ m → ℤ
sumℤ []       = + 0
sumℤ (x ∷ xs) = x + sumℤ xs

------------------------------------------------------------------------
-- Masked quadratic and weighted dot

Qσ : ∀ {m : Nat} → Vec Sign m → Vec Trit m → ℤ
Qσ σ x =
  sumℤ (zipWith (λ s xi → signℤ s * sqℤ (toℤTrit xi)) σ x)

dotσ : ∀ {m : Nat} → Vec Sign m → Vec Trit m → Vec Trit m → ℤ
dotσ σ x y =
  sumℤ (zipWith (λ s p → signℤ s * (proj₁ p * proj₂ p))
                σ
                (zipWith (λ a b → (toℤTrit a , toℤTrit b)) x y))

------------------------------------------------------------------------
-- Polarization (B₂) written directly as a signed sum of per-coordinate
-- (a+b)^2 - a^2 - b^2. This is definitionally equivalent to
-- Qσ(x+y)-Qσ(x)-Qσ(y), but avoids Trit addition issues.

B2σ : ∀ {m : Nat} → Vec Sign m → Vec Trit m → Vec Trit m → ℤ
B2σ [] [] [] = + 0
B2σ (s ∷ σ) (a ∷ x) (b ∷ y) =
  signℤ s *
    ((toℤTrit a + toℤTrit b) * (toℤTrit a + toℤTrit b)
      - (toℤTrit a * toℤTrit a)
      - (toℤTrit b * toℤTrit b))
  + B2σ σ x y

------------------------------------------------------------------------
-- Scalar identity: (a+b)^2 - a^2 - b^2 = 2ab for Trit values

b2-trit :
  (a b : Trit) →
  (toℤTrit a + toℤTrit b) * (toℤTrit a + toℤTrit b)
    - (toℤTrit a * toℤTrit a)
    - (toℤTrit b * toℤTrit b)
    ≡ (+ 2) * (toℤTrit a * toℤTrit b)
b2-trit neg neg = refl
b2-trit neg zer = refl
b2-trit neg pos = refl
b2-trit zer neg = refl
b2-trit zer zer = refl
b2-trit zer pos = refl
b2-trit pos neg = refl
b2-trit pos zer = refl
b2-trit pos pos = refl

swap2 :
  ∀ (s : Sign) (z : ℤ) →
  signℤ s * ((+ 2) * z) ≡ (+ 2) * (signℤ s * z)
swap2 plus z =
  begin
    signℤ plus * ((+ 2) * z)
  ≡⟨ IntP.*-identityˡ ((+ 2) * z) ⟩
    (+ 2) * z
  ≡⟨ cong (λ t → (+ 2) * t) (sym (IntP.*-identityˡ z)) ⟩
    (+ 2) * (signℤ plus * z)
  ∎
swap2 minus z =
  let
    step1a : signℤ minus * ((+ 2) * z) ≡ - ((+ 1) * ((+ 2) * z))
    step1a = sym (IntP.neg-distribˡ-* (+ 1) ((+ 2) * z))

    step1b : - ((+ 1) * ((+ 2) * z)) ≡ - ((+ 2) * z)
    step1b = cong (λ t → - t) (IntP.*-identityˡ ((+ 2) * z))

    step1 : signℤ minus * ((+ 2) * z) ≡ - ((+ 2) * z)
    step1 = trans step1a step1b

    step2 : - ((+ 2) * z) ≡ (+ 2) * (- z)
    step2 = IntP.neg-distribʳ-* (+ 2) z

    step3a : - z ≡ - ((+ 1) * z)
    step3a = cong (λ t → - t) (sym (IntP.*-identityˡ z))

    step3b : - ((+ 1) * z) ≡ (- (+ 1)) * z
    step3b = IntP.neg-distribˡ-* (+ 1) z

    step3 : - z ≡ (signℤ minus * z)
    step3 = trans step3a step3b
  in
  trans step1 (trans step2 (cong (λ t → (+ 2) * t) step3))

------------------------------------------------------------------------
-- Polarization result: B₂σ = 2 · dotσ

B2σ≡2dotσ :
  ∀ {m : Nat} (σ : Vec Sign m) (x y : Vec Trit m) →
  B2σ σ x y ≡ (+ 2) * dotσ σ x y
B2σ≡2dotσ [] [] [] = refl
B2σ≡2dotσ (s ∷ σ) (a ∷ x) (b ∷ y) =
  let
    xa = toℤTrit a
    yb = toℤTrit b
  in
  begin
    B2σ (s ∷ σ) (a ∷ x) (b ∷ y)
  ≡⟨ cong (λ t → signℤ s * t + B2σ σ x y) (b2-trit a b) ⟩
    signℤ s * ((+ 2) * (xa * yb)) + B2σ σ x y
  ≡⟨ cong (λ t → signℤ s * ((+ 2) * (xa * yb)) + t) (B2σ≡2dotσ σ x y) ⟩
    signℤ s * ((+ 2) * (xa * yb)) + (+ 2) * dotσ σ x y
  ≡⟨ cong (λ t → t + (+ 2) * dotσ σ x y)
        (swap2 s (xa * yb)) ⟩
    (+ 2) * (signℤ s * (xa * yb)) + (+ 2) * dotσ σ x y
  ≡⟨ sym (IntP.*-distribˡ-+ (+ 2) (signℤ s * (xa * yb)) (dotσ σ x y)) ⟩
    (+ 2) * (signℤ s * (xa * yb) + dotσ σ x y)
  ≡⟨ refl ⟩
    (+ 2) * dotσ (s ∷ σ) (a ∷ x) (b ∷ y)
  ∎
  where
    infix 0 ▸
    ▸ : ∀ {A : Set} {u v : A} → u ≡ v → u ≡ v
    ▸ p = p
