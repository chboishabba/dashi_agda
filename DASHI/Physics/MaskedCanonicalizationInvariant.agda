module DASHI.Physics.MaskedCanonicalizationInvariant where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Relation.Binary.PropositionalEquality using (cong)

open import Data.Vec using (Vec; []; _∷_)
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
