module DASHI.Physics.MaskedQuadraticRenormalization where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import Data.Vec using (Vec; _++_; zipWith)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Integer using (ℤ; _*_) renaming (_+_ to _+ℤ_)

open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Physics.TailCollapseProof as TCP
open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ
open import DASHI.Physics.MaskedSplitQuadratic as MSQ

------------------------------------------------------------------------
-- Basic split lemmas for coarse/tail under concatenation

coarseOf-++ :
  ∀ (m k : Nat) (c : Vec Trit m) (t : Vec Trit k) →
  TCP.coarseOf m k (c ++ t) ≡ c
coarseOf-++ m k c t
  rewrite TCP.split-++ m k c t
  = refl

tailOf-++ :
  ∀ (m k : Nat) (c : Vec Trit m) (t : Vec Trit k) →
  TCP.tailOf m k (c ++ t) ≡ t
tailOf-++ m k c t
  rewrite TCP.split-++ m k c t
  = refl

------------------------------------------------------------------------
-- Coarse/tail behavior under renormalization Rᵣ

coarseOf-Rᵣ :
  ∀ (m k : Nat) (x : Vec Trit (m + k)) →
  TCP.coarseOf m k (TCP.Rᵣ {m} {k} x) ≡ TCP.coarseOf m k x
coarseOf-Rᵣ m k x with TCP.split m k x
... | (c , t)
  rewrite sym (TCP.merge-split m k x)
        | TCP.Rᵣ-++ m k c t
        | coarseOf-++ m k c (TCP.shiftTail t)
  = refl

tailOf-Rᵣ :
  ∀ (m k : Nat) (x : Vec Trit (m + k)) →
  TCP.tailOf m k (TCP.Rᵣ {m} {k} x) ≡ TCP.shiftTail (TCP.tailOf m k x)
tailOf-Rᵣ m k x with TCP.split m k x
... | (c , t)
  rewrite sym (TCP.merge-split m k x)
        | TCP.Rᵣ-++ m k c t
        | tailOf-++ m k c (TCP.shiftTail t)
  = refl

Rᵣ-decomp :
  ∀ (m k : Nat) (x : Vec Trit (m + k)) →
  TCP.Rᵣ {m} {k} x ≡ TCP.coarseOf m k x ++ TCP.shiftTail (TCP.tailOf m k x)
Rᵣ-decomp m k x with TCP.split m k x
... | (c , t)
  rewrite sym (TCP.merge-split m k x)
        | TCP.Rᵣ-++ m k c t
        | coarseOf-++ m k c t
        | tailOf-++ m k c t
  = refl

------------------------------------------------------------------------
-- Masked quadratic under renormalization:
-- Qσ(Rᵣ x) splits into coarse + shifted tail.

Qσ-split-++ :
  ∀ (m k : Nat)
    (σc : Vec IMQ.Sign m) (σt : Vec IMQ.Sign k)
    (c : Vec Trit m) (t : Vec Trit k) →
  IMQ.Qσ (σc ++ σt) (c ++ t)
    ≡ IMQ.Qσ σc c +ℤ IMQ.Qσ σt t
Qσ-split-++ m k σc σt c t =
  let
    f = (λ s xi → IMQ.signℤ s * IMQ.sqℤ (IMQ.toℤTrit xi))
  in
  trans
    refl
    (trans
      (cong IMQ.sumℤ (MSQ.zipWith-++ f σc σt c t))
      (trans
        (MSQ.sumℤ-++ (zipWith f σc c) (zipWith f σt t))
        refl))

Qσ-split-coarse :
  ∀ (m k : Nat)
    (σ : Vec IMQ.Sign (m + k))
    (c : Vec Trit m) (t : Vec Trit k) →
  IMQ.Qσ σ (c ++ t)
    ≡ IMQ.Qσ (TCP.coarseOf m k σ) c
    +ℤ IMQ.Qσ (TCP.tailOf m k σ) t
Qσ-split-coarse m k σ c t
  =
  trans
    (cong (λ z → IMQ.Qσ z (c ++ t)) (sym (TCP.merge-split {A = IMQ.Sign} m k σ)))
    (Qσ-split-++ m k (TCP.coarseOf m k σ) (TCP.tailOf m k σ) c t)

Qσ-R :
  ∀ (m k : Nat)
    (σ : Vec IMQ.Sign (m + k))
    (x : Vec Trit (m + k)) →
  IMQ.Qσ σ (TCP.Rᵣ {m} {k} x)
    ≡ IMQ.Qσ (TCP.coarseOf m k σ) (TCP.coarseOf m k x)
    +ℤ IMQ.Qσ (TCP.tailOf   m k σ) (TCP.shiftTail (TCP.tailOf m k x))
Qσ-R m k σ x with TCP.split m k x
... | (c , t)
  rewrite sym (TCP.merge-split m k x)
        | TCP.Rᵣ-++ m k c t
  = Qσ-split-coarse m k σ c (TCP.shiftTail t)
