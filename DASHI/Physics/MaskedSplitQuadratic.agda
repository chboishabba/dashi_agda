module DASHI.Physics.MaskedSplitQuadratic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import Data.Vec using (Vec; []; _∷_; _++_; zipWith)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Integer using (ℤ; _*_) renaming (_+_ to _+ℤ_)
open import Data.Integer.Properties as IntP

open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ
open import DASHI.Physics.TailCollapseProof as TCP
open import DASHI.Algebra.Trit using (Trit)

------------------------------------------------------------------------
-- sumℤ distributes over ++

sumℤ-++ :
  ∀ {m k : Nat} (xs : Vec ℤ m) (ys : Vec ℤ k) →
  IMQ.sumℤ (xs ++ ys) ≡ IMQ.sumℤ xs +ℤ IMQ.sumℤ ys
sumℤ-++ [] ys =
  sym (IntP.+-identityˡ (IMQ.sumℤ ys))
sumℤ-++ (x ∷ xs) ys =
  let
    sumℤ-cons : IMQ.sumℤ (x ∷ xs) ≡ x +ℤ IMQ.sumℤ xs
    sumℤ-cons = refl
    step : x +ℤ IMQ.sumℤ (xs ++ ys) ≡ x +ℤ (IMQ.sumℤ xs +ℤ IMQ.sumℤ ys)
    step = cong (λ z → x +ℤ z) (sumℤ-++ xs ys)
    step2 : x +ℤ (IMQ.sumℤ xs +ℤ IMQ.sumℤ ys) ≡ (x +ℤ IMQ.sumℤ xs) +ℤ IMQ.sumℤ ys
    step2 = sym (IntP.+-assoc x (IMQ.sumℤ xs) (IMQ.sumℤ ys))
    step3 : (x +ℤ IMQ.sumℤ xs) +ℤ IMQ.sumℤ ys ≡ IMQ.sumℤ (x ∷ xs) +ℤ IMQ.sumℤ ys
    step3 = cong (λ z → z +ℤ IMQ.sumℤ ys) (sym sumℤ-cons)
  in
  trans step (trans step2 step3)

------------------------------------------------------------------------
-- zipWith distributes over ++

zipWith-++ :
  ∀ {A B C : Set} (f : A → B → C)
    {m k : Nat}
    (a₁ : Vec A m) (a₂ : Vec A k)
    (b₁ : Vec B m) (b₂ : Vec B k) →
  zipWith f (a₁ ++ a₂) (b₁ ++ b₂) ≡ (zipWith f a₁ b₁) ++ (zipWith f a₂ b₂)
zipWith-++ f [] a₂ [] b₂ = refl
zipWith-++ f (a ∷ a₁) a₂ (b ∷ b₁) b₂ =
  cong (λ z → f a b ∷ z) (zipWith-++ f a₁ a₂ b₁ b₂)

------------------------------------------------------------------------
-- Masked quadratic split: Qσ splits over (coarse ++ tail)

Qσ-split :
  ∀ (m k : Nat)
    (σ : Vec IMQ.Sign (m + k))
    (x : Vec Trit (m + k)) →
  IMQ.Qσ σ x
    ≡ IMQ.Qσ (TCP.coarseOf m k σ) (TCP.coarseOf m k x)
    +ℤ IMQ.Qσ (TCP.tailOf   m k σ) (TCP.tailOf   m k x)
Qσ-split m k σ x =
  let
    f = (λ s t → IMQ.signℤ s * IMQ.sqℤ (IMQ.toℤTrit t))
    σc = TCP.coarseOf m k σ
    σt = TCP.tailOf m k σ
    xc = TCP.coarseOf m k x
    xt = TCP.tailOf m k x
    σ≡ : σc ++ σt ≡ σ
    σ≡ = TCP.merge-split m k σ
    x≡ : xc ++ xt ≡ x
    x≡ = TCP.merge-split m k x
    step1 : IMQ.Qσ σ x ≡ IMQ.sumℤ (zipWith f (σc ++ σt) x)
    step1 = cong (λ z → IMQ.sumℤ (zipWith f z x)) (sym σ≡)
    step2 : IMQ.sumℤ (zipWith f (σc ++ σt) x) ≡ IMQ.sumℤ (zipWith f (σc ++ σt) (xc ++ xt))
    step2 = cong (λ z → IMQ.sumℤ (zipWith f (σc ++ σt) z)) (sym x≡)
    step3 : IMQ.sumℤ (zipWith f (σc ++ σt) (xc ++ xt))
            ≡ IMQ.sumℤ ((zipWith f σc xc) ++ (zipWith f σt xt))
    step3 = cong IMQ.sumℤ (zipWith-++ f σc σt xc xt)
    step4 : IMQ.sumℤ ((zipWith f σc xc) ++ (zipWith f σt xt))
            ≡ IMQ.sumℤ (zipWith f σc xc) +ℤ IMQ.sumℤ (zipWith f σt xt)
    step4 = sumℤ-++ (zipWith f σc xc) (zipWith f σt xt)
  in
  trans step1 (trans step2 (trans step3 step4))
