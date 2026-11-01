module DASHI.Physics.MaskedQuadraticInvariance where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong)

open import Data.Vec using (Vec; []; _∷_)
open import Data.Integer using (ℤ; _*_; _+_)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ
open import DASHI.Physics.CanonicalizationMinimal as CM

------------------------------------------------------------------------
-- Canonicalization preserves masked quadratic

sqT : Trit → ℤ
sqT t = IMQ.sqℤ (IMQ.toℤTrit t)

sqT-canon : ∀ t → sqT (CM.canonTrit t) ≡ sqT t
sqT-canon neg = refl
sqT-canon zer = refl
sqT-canon pos = refl

Qσ-canon :
  ∀ {m : Nat} (σ : Vec IMQ.Sign m) (x : Vec Trit m) →
  IMQ.Qσ σ (CM.canonVec x) ≡ IMQ.Qσ σ x
Qσ-canon [] [] = refl
Qσ-canon (s ∷ σ) (t ∷ x)
  rewrite sqT-canon t
  = cong (λ z → IMQ.signℤ s * sqT t + z) (Qσ-canon σ x)
