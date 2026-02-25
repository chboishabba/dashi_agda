module DASHI.Physics.MaskedOrthogonalSplitConstructive where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import Data.Vec using (Vec; []; _∷_; _++_; zipWith)
open import Data.Product using (_×_; _,_)
open import Data.Integer using (ℤ; _*_; +_; 0ℤ) renaming (_+_ to _+ℤ_)
open import Data.Integer.Properties as IntP

open import DASHI.Algebra.Trit using (Trit; zer)
open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ

------------------------------------------------------------------------
-- Zero vectors

zeros : ∀ {n : Nat} → Vec Trit n
zeros {n = zero}  = []
zeros {n = suc n} = zer ∷ zeros {n = n}

embedCore : ∀ {m k : Nat} → Vec Trit m → Vec Trit (m + k)
embedCore {m} {k} c = c ++ zeros {n = k}

embedTail : ∀ {m k : Nat} → Vec Trit k → Vec Trit (m + k)
embedTail {m} {k} t = zeros {n = m} ++ t

------------------------------------------------------------------------
-- dotσ unfolds to a recursive definition

dotσ-cons :
  ∀ {m : Nat} (s : IMQ.Sign) (σ : Vec IMQ.Sign m)
    (x : Trit) (xs : Vec Trit m)
    (y : Trit) (ys : Vec Trit m) →
  IMQ.dotσ (s ∷ σ) (x ∷ xs) (y ∷ ys)
    ≡ (IMQ.signℤ s * (IMQ.toℤTrit x * IMQ.toℤTrit y)) +ℤ IMQ.dotσ σ xs ys
dotσ-cons s σ x xs y ys = refl

------------------------------------------------------------------------
-- dotσ against a zero vector is 0

dotσ-zero-left :
  ∀ {m : Nat} (σ : Vec IMQ.Sign m) (y : Vec Trit m) →
  IMQ.dotσ σ (zeros {n = m}) y ≡ 0ℤ
dotσ-zero-left [] [] = refl
dotσ-zero-left (s ∷ σ) (y ∷ ys) =
  trans
    (dotσ-cons s σ zer (zeros {n = _}) y ys)
    (trans
    (cong (λ z → z +ℤ IMQ.dotσ σ (zeros {n = _}) ys)
            (trans
              (cong (λ t → IMQ.signℤ s * t) (IntP.*-zeroˡ (IMQ.toℤTrit y)))
              (IntP.*-zeroʳ (IMQ.signℤ s))))
      (cong (λ z → 0ℤ +ℤ z) (dotσ-zero-left σ ys)))

------------------------------------------------------------------------
-- Core and tail are orthogonal under dotσ

dotσ-core⊥tail :
  ∀ {m k : Nat} (σ : Vec IMQ.Sign (m + k))
    (c : Vec Trit m) (t : Vec Trit k) →
  IMQ.dotσ σ (embedCore {m} {k} c) (embedTail {m} {k} t) ≡ 0ℤ
dotσ-core⊥tail {zero} {k} σ [] t = dotσ-zero-left σ t
dotσ-core⊥tail {suc m} {k} (s ∷ σ) (x ∷ xs) t =
  trans
    (dotσ-cons s σ x (xs ++ zeros {n = k}) zer (zeros {n = m} ++ t))
    (trans
    (cong (λ z → z +ℤ IMQ.dotσ σ (xs ++ zeros {n = k}) (zeros {n = m} ++ t))
            (trans
              (cong (λ t → IMQ.signℤ s * t) (IntP.*-zeroʳ (IMQ.toℤTrit x)))
              (IntP.*-zeroʳ (IMQ.signℤ s))))
      (cong (λ z → 0ℤ +ℤ z) (dotσ-core⊥tail {m} {k} σ xs t)))

------------------------------------------------------------------------
-- Therefore B2σ is also 0 on core/tail blocks

B2σ-core⊥tail :
  ∀ {m k : Nat} (σ : Vec IMQ.Sign (m + k))
    (c : Vec Trit m) (t : Vec Trit k) →
  IMQ.B2σ σ (embedCore {m} {k} c) (embedTail {m} {k} t) ≡ 0ℤ
B2σ-core⊥tail {m} {k} σ c t =
  trans (IMQ.B2σ≡2dotσ σ (embedCore {m} {k} c) (embedTail {m} {k} t))
        (cong (λ z → (+ 2) * z) (dotσ-core⊥tail σ c t))
