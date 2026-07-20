module DASHI.Physics.MaskedCanonicalizationInvariant where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import Data.Vec using (Vec; []; _∷_; _++_)
open import Data.Integer using (ℤ; _+_; _*_)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import DASHI.Physics.CanonicalizationMinimal as CM
open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ
open import DASHI.Physics.TailCollapseProof as TCP

------------------------------------------------------------------------
-- Canonicalization changes representatives, not masked magnitude.

sq-canonTrit : ∀ t → IMQ.sqℤ (IMQ.toℤTrit (CM.canonTrit t)) ≡ IMQ.sqℤ (IMQ.toℤTrit t)
sq-canonTrit neg = refl
sq-canonTrit zer = refl
sq-canonTrit pos = refl

Qσ-canonVec :
  ∀ {m : Nat} (σ : Vec IMQ.Sign m) (x : Vec Trit m) →
  IMQ.Qσ σ (CM.canonVec x) ≡ IMQ.Qσ σ x
Qσ-canonVec [] [] = refl
Qσ-canonVec (s ∷ σ) (t ∷ x)
  rewrite sq-canonTrit t
  = cong (λ q → IMQ.signℤ s * IMQ.sqℤ (IMQ.toℤTrit t) + q)
         (Qσ-canonVec σ x)

------------------------------------------------------------------------
-- The full-state canonicalizer acts only on the coarse block.

coreQσ :
  ∀ {m k : Nat} →
  Vec IMQ.Sign m → Vec Trit (m + k) → ℤ
coreQσ {m} {k} σ x = IMQ.Qσ σ (TCP.coarseOf m k x)

coreQσ-Cᵣ :
  ∀ {m k : Nat}
    (σ : Vec IMQ.Sign m)
    (x : Vec Trit (m + k)) →
  coreQσ σ (CM.Cᵣ {m} {k} x) ≡ coreQσ σ x
coreQσ-Cᵣ {m} {k} σ x with TCP.split m k x
... | (c , t)
  rewrite CM.Cᵣ-++ c t
        | TCP.split-++ m k (CM.canonVec c) t
  = Qσ-canonVec σ c

------------------------------------------------------------------------
-- Canonicalization also preserves the induced masked bilinear form when
-- applied to both arguments.

product-canonTrit :
  ∀ a b →
  IMQ.toℤTrit (CM.canonTrit a) * IMQ.toℤTrit (CM.canonTrit b)
    ≡ IMQ.toℤTrit a * IMQ.toℤTrit b
product-canonTrit neg neg = refl
product-canonTrit neg zer = refl
product-canonTrit neg pos = refl
product-canonTrit zer neg = refl
product-canonTrit zer zer = refl
product-canonTrit zer pos = refl
product-canonTrit pos neg = refl
product-canonTrit pos zer = refl
product-canonTrit pos pos = refl

dotσ-canonVec₂ :
  ∀ {m : Nat} (σ : Vec IMQ.Sign m) (x y : Vec Trit m) →
  IMQ.dotσ σ (CM.canonVec x) (CM.canonVec y) ≡ IMQ.dotσ σ x y
dotσ-canonVec₂ [] [] [] = refl
dotσ-canonVec₂ (s ∷ σ) (a ∷ x) (b ∷ y)
  rewrite product-canonTrit a b
  = cong (λ q → IMQ.signℤ s * (IMQ.toℤTrit a * IMQ.toℤTrit b) + q)
         (dotσ-canonVec₂ σ x y)
