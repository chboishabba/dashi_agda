module DASHI.Physics.MaskedBlockOrthogonality where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

open import Data.Vec using (Vec; []; _∷_; _++_)
open import Data.Integer using (ℤ; _+_; _-_; _*_; +_)

open import DASHI.Algebra.Trit using (Trit; zer)
open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ

------------------------------------------------------------------------
-- Neutral vectors and block embeddings.

zeroTrits : ∀ (n : Nat) → Vec Trit n
zeroTrits zero = []
zeroTrits (suc n) = zer ∷ zeroTrits n

embedCore :
  ∀ {m k : Nat} → Vec Trit m → Vec Trit (m + k)
embedCore {m} {k} c = c ++ zeroTrits k

embedTail :
  ∀ {m k : Nat} → Vec Trit k → Vec Trit (m + k)
embedTail {m} {k} t = zeroTrits m ++ t

------------------------------------------------------------------------
-- Diagonal masked forms split exactly across concatenated blocks.

Qσ-++ :
  ∀ {m k : Nat}
    (σc : Vec IMQ.Sign m) (σt : Vec IMQ.Sign k)
    (c : Vec Trit m) (t : Vec Trit k) →
  IMQ.Qσ (σc ++ σt) (c ++ t)
    ≡ IMQ.Qσ σc c + IMQ.Qσ σt t
Qσ-++ [] σt [] t = refl
Qσ-++ (s ∷ σc) σt (x ∷ c) t =
  cong (λ q → IMQ.signℤ s * IMQ.sqℤ (IMQ.toℤTrit x) + q)
       (Qσ-++ σc σt c t)

dotσ-++ :
  ∀ {m k : Nat}
    (σc : Vec IMQ.Sign m) (σt : Vec IMQ.Sign k)
    (c₁ c₂ : Vec Trit m) (t₁ t₂ : Vec Trit k) →
  IMQ.dotσ (σc ++ σt) (c₁ ++ t₁) (c₂ ++ t₂)
    ≡ IMQ.dotσ σc c₁ c₂ + IMQ.dotσ σt t₁ t₂
dotσ-++ [] σt [] [] t₁ t₂ = refl
dotσ-++ (s ∷ σc) σt (x₁ ∷ c₁) (x₂ ∷ c₂) t₁ t₂ =
  cong
    (λ q → IMQ.signℤ s * (IMQ.toℤTrit x₁ * IMQ.toℤTrit x₂) + q)
    (dotσ-++ σc σt c₁ c₂ t₁ t₂)

B2σ-++ :
  ∀ {m k : Nat}
    (σc : Vec IMQ.Sign m) (σt : Vec IMQ.Sign k)
    (c₁ c₂ : Vec Trit m) (t₁ t₂ : Vec Trit k) →
  IMQ.B2σ (σc ++ σt) (c₁ ++ t₁) (c₂ ++ t₂)
    ≡ IMQ.B2σ σc c₁ c₂ + IMQ.B2σ σt t₁ t₂
B2σ-++ [] σt [] [] t₁ t₂ = refl
B2σ-++ (s ∷ σc) σt (a₁ ∷ c₁) (a₂ ∷ c₂) t₁ t₂ =
  cong
    (λ q →
      IMQ.signℤ s *
        ((IMQ.toℤTrit a₁ + IMQ.toℤTrit a₂) *
           (IMQ.toℤTrit a₁ + IMQ.toℤTrit a₂)
         - (IMQ.toℤTrit a₁ * IMQ.toℤTrit a₁)
         - (IMQ.toℤTrit a₂ * IMQ.toℤTrit a₂))
      + q)
    (B2σ-++ σc σt c₁ c₂ t₁ t₂)

------------------------------------------------------------------------
-- Neutral blocks contribute zero to the bilinear form.

dotσ-zero-left :
  ∀ {n : Nat} (σ : Vec IMQ.Sign n) (x : Vec Trit n) →
  IMQ.dotσ σ (zeroTrits n) x ≡ + 0
dotσ-zero-left [] [] = refl
dotσ-zero-left (s ∷ σ) (x ∷ xs) = dotσ-zero-left σ xs

dotσ-zero-right :
  ∀ {n : Nat} (σ : Vec IMQ.Sign n) (x : Vec Trit n) →
  IMQ.dotσ σ x (zeroTrits n) ≡ + 0
dotσ-zero-right [] [] = refl
dotσ-zero-right (s ∷ σ) (x ∷ xs) = dotσ-zero-right σ xs

core⊥tail-dotσ :
  ∀ {m k : Nat}
    (σc : Vec IMQ.Sign m) (σt : Vec IMQ.Sign k)
    (c : Vec Trit m) (t : Vec Trit k) →
  IMQ.dotσ (σc ++ σt)
    (embedCore {m} {k} c)
    (embedTail {m} {k} t)
    ≡ + 0
core⊥tail-dotσ {m} {k} σc σt c t =
  trans
    (dotσ-++ σc σt c (zeroTrits m) (zeroTrits k) t)
    (cong₂ _+_ (dotσ-zero-right σc c) (dotσ-zero-left σt t))

core⊥tail-B2σ :
  ∀ {m k : Nat}
    (σc : Vec IMQ.Sign m) (σt : Vec IMQ.Sign k)
    (c : Vec Trit m) (t : Vec Trit k) →
  IMQ.B2σ (σc ++ σt)
    (embedCore {m} {k} c)
    (embedTail {m} {k} t)
    ≡ + 0
core⊥tail-B2σ {m} {k} σc σt c t =
  trans
    (IMQ.B2σ≡2dotσ
      (σc ++ σt)
      (embedCore {m} {k} c)
      (embedTail {m} {k} t))
    (cong (λ q → (+ 2) * q) (core⊥tail-dotσ σc σt c t))

------------------------------------------------------------------------
-- Concrete witness corresponding to the abstract MaskedOrthogonalSplit gate.

record ConcreteMaskedOrthogonalSplit {m k : Nat}
  (σc : Vec IMQ.Sign m) (σt : Vec IMQ.Sign k) : Set where
  field
    quadratic-additive :
      ∀ c t →
      IMQ.Qσ (σc ++ σt) (c ++ t)
        ≡ IMQ.Qσ σc c + IMQ.Qσ σt t

    core-orthogonal-tail :
      ∀ c t →
      IMQ.B2σ (σc ++ σt)
        (embedCore {m} {k} c)
        (embedTail {m} {k} t)
        ≡ + 0

concreteMaskedOrthogonalSplit :
  ∀ {m k : Nat}
    (σc : Vec IMQ.Sign m) (σt : Vec IMQ.Sign k) →
  ConcreteMaskedOrthogonalSplit σc σt
concreteMaskedOrthogonalSplit σc σt =
  record
    { quadratic-additive = Qσ-++ σc σt
    ; core-orthogonal-tail = core⊥tail-B2σ σc σt
    }
