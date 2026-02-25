module DASHI.Physics.TailCollapseProof where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_; _++_; replicate)
open import Data.Vec.Base using (take; init; last; _∷ʳ_)
open import DASHI.Algebra.Trit using (Trit; zer)

------------------------------------------------------------------------
-- A concrete, nontrivial renormalization Rᵣ implementing a “scale shift”
------------------------------------------------------------------------

split :
  ∀ {A : Set} (m k : Nat) →
  Vec A (m + k) → (Vec A m × Vec A k)
split {A} zero    k xs       = ([] , xs)
split {A} (suc m) k (x ∷ xs) with split {A} m k xs
... | (c , t) = (x ∷ c , t)

split-++ :
  ∀ {A : Set} (m k : Nat) (c : Vec A m) (t : Vec A k) →
  split m k (c ++ t) ≡ (c , t)
split-++ zero k [] t = refl
split-++ (suc m) k (x ∷ xs) t =
  cong (λ p → (x ∷ proj₁ p , proj₂ p)) (split-++ m k xs t)

coarseOf : ∀ {A : Set} (m k : Nat) → Vec A (m + k) → Vec A m
coarseOf m k x = proj₁ (split m k x)

tailOf : ∀ {A : Set} (m k : Nat) → Vec A (m + k) → Vec A k
tailOf m k x = proj₂ (split m k x)

------------------------------------------------------------------------
-- Tail-band operators

shiftTail : ∀ {k : Nat} → Vec Trit k → Vec Trit k
shiftTail {zero}    []       = []
shiftTail {suc k′}  (x ∷ xs) = xs ∷ʳ zer

projTail : ∀ {k : Nat} → Vec Trit k → Vec Trit k
projTail {zero}    []       = []
projTail {suc k′}  t        = (init t) ∷ʳ zer


tailStep : ∀ {k : Nat} → Vec Trit k → Vec Trit k
tailStep t = projTail (shiftTail t)

------------------------------------------------------------------------
-- Lift tail-band operators to full state

Rᵣ : ∀ {m k : Nat} → Vec Trit (m + k) → Vec Trit (m + k)
Rᵣ {m} {k} x with split m k x
... | (c , t) = c ++ shiftTail t

Pᵣ : ∀ {m k : Nat} → Vec Trit (m + k) → Vec Trit (m + k)
Pᵣ {m} {k} x with split m k x
... | (c , t) = c ++ projTail t

Rᵣ-++ :
  ∀ (m k : Nat) (c : Vec Trit m) (t : Vec Trit k) →
  Rᵣ {m} {k} (c ++ t) ≡ c ++ shiftTail t
Rᵣ-++ m k c t rewrite split-++ m k c t = refl

Pᵣ-++ :
  ∀ (m k : Nat) (c : Vec Trit m) (t : Vec Trit k) →
  Pᵣ {m} {k} (c ++ t) ≡ c ++ projTail t
Pᵣ-++ m k c t rewrite split-++ m k c t = refl


Tᵣ : ∀ {m k : Nat} → Vec Trit (m + k) → Vec Trit (m + k)
Tᵣ {m} {k} x = Pᵣ {m} {k} (Rᵣ {m} {k} x)

------------------------------------------------------------------------
-- Iteration

iterate : ∀ {A : Set} → Nat → (A → A) → A → A
iterate zero    f x = x
iterate (suc n) f x = iterate n f (f x)

------------------------------------------------------------------------
-- Finite-time tail collapse

------------------------------------------------------------------------
-- Helper lemmas for replicate

init-replicate :
  ∀ {k : Nat} → init (replicate (suc k) zer) ≡ replicate k zer
init-replicate {zero} = refl
init-replicate {suc k} =
  cong (λ t → zer ∷ t) (init-replicate {k})

snoc-replicate :
  ∀ {k : Nat} → (replicate k zer) ∷ʳ zer ≡ replicate (suc k) zer
snoc-replicate {zero} = refl
snoc-replicate {suc k} =
  cong (λ t → zer ∷ t) (snoc-replicate {k})

tailStep-forgets-last :
  ∀ {k′ : Nat} (t : Vec Trit (suc k′)) →
  tailStep t ≡ projTail (shiftTail t)
tailStep-forgets-last {k′} t = refl

projTail-replicate :
  ∀ {k : Nat} → projTail (replicate k zer) ≡ replicate k zer
projTail-replicate {zero}    = refl
projTail-replicate {suc k′}  =
  trans
    (cong (_∷ʳ zer) (init-replicate {k′}))
    (snoc-replicate {k′})

shiftTail-replicate :
  ∀ {k : Nat} → shiftTail (replicate k zer) ≡ replicate k zer
shiftTail-replicate {zero}   = refl
shiftTail-replicate {suc k′} =
  snoc-replicate {k′}

tailStep-replicate :
  ∀ {k : Nat} → tailStep (replicate k zer) ≡ replicate k zer
tailStep-replicate {k} =
  trans (cong projTail (shiftTail-replicate {k}))
        (projTail-replicate {k})

------------------------------------------------------------------------
-- Extra Vec lemmas needed for constructive nilpotence
------------------------------------------------------------------------

pair-η : ∀ {A B : Set} (p : A × B) → (proj₁ p , proj₂ p) ≡ p
pair-η (a , b) = refl

init-∷ʳ : ∀ {A : Set} {n : Nat} (xs : Vec A n) (a : A) → init (xs ∷ʳ a) ≡ xs
init-∷ʳ {n = zero}    []       a = refl
init-∷ʳ {n = suc n} (x ∷ xs) a rewrite init-∷ʳ xs a = refl

projTail-idem :
  ∀ {k : Nat} (t : Vec Trit k) → projTail (projTail t) ≡ projTail t
projTail-idem {zero} [] = refl
projTail-idem {suc k′} t =
  trans
    (cong (_∷ʳ zer) (init-∷ʳ (init t) zer))
    refl

Pᵣ-idem :
  ∀ (m k : Nat) (x : Vec Trit (m + k)) →
  Pᵣ {m} {k} (Pᵣ {m} {k} x) ≡ Pᵣ {m} {k} x
Pᵣ-idem m k x with split m k x
... | (c , t)
  rewrite Pᵣ-++ m k c t
        | Pᵣ-++ m k c (projTail t)
        | projTail-idem t
  = refl

tailStep≡shiftTail : ∀ {k : Nat} (t : Vec Trit k) → tailStep t ≡ shiftTail t
tailStep≡shiftTail {zero}    [] = refl
tailStep≡shiftTail {suc k′} (x ∷ xs)
  rewrite init-∷ʳ xs zer
  = refl

shiftTail-∷ʳ-zer :
  ∀ {k : Nat} (xs : Vec Trit k) →
  shiftTail (xs ∷ʳ zer) ≡ (shiftTail xs) ∷ʳ zer
shiftTail-∷ʳ-zer {zero} [] = refl
shiftTail-∷ʳ-zer {suc k} (x ∷ xs) = refl

iterate-shiftTail-∷ʳ-zer :
  ∀ {k : Nat} (n : Nat) (xs : Vec Trit k) →
  iterate n shiftTail (xs ∷ʳ zer) ≡ (iterate n shiftTail xs) ∷ʳ zer
iterate-shiftTail-∷ʳ-zer zero xs = refl
iterate-shiftTail-∷ʳ-zer (suc n) xs
  rewrite shiftTail-∷ʳ-zer xs
        | iterate-shiftTail-∷ʳ-zer n (shiftTail xs)
  = refl

iterate-pointwise :
  ∀ {A : Set} (n : Nat) (f g : A → A) (x : A) →
  (∀ y → f y ≡ g y) →
  iterate n f x ≡ iterate n g x
iterate-pointwise zero f g x fg = refl
iterate-pointwise (suc n) f g x fg
  rewrite fg x
  = iterate-pointwise n f g (g x) fg

------------------------------------------------------------------------
-- Finite-time tail collapse (constructive)
------------------------------------------------------------------------

tailCollapse-shiftTail :
  ∀ (k : Nat) (t : Vec Trit k) →
  iterate k shiftTail t ≡ replicate k zer
tailCollapse-shiftTail zero    []       = refl
tailCollapse-shiftTail (suc k) (x ∷ xs) =
  trans
    (iterate-shiftTail-∷ʳ-zer k xs)
    (trans
      (cong (_∷ʳ zer) (tailCollapse-shiftTail k xs))
      (snoc-replicate {k}))

tailCollapse :
  ∀ (k : Nat) (t : Vec Trit k) →
  iterate k tailStep t ≡ replicate k zer
tailCollapse k t =
  trans
    (iterate-pointwise k tailStep shiftTail t (λ y → tailStep≡shiftTail y))
    (tailCollapse-shiftTail k t)

------------------------------------------------------------------------
-- Lifted corollary: full state tail band collapses in k steps

------------------------------------------------------------------------
-- Lifted corollary: full state tail band collapses in k steps (constructive)
------------------------------------------------------------------------

merge-split :
  ∀ {A : Set} (m k : Nat) (x : Vec A (m + k)) →
  (coarseOf m k x ++ tailOf m k x) ≡ x
merge-split {A} zero    k x = refl
merge-split {A} (suc m) k (x ∷ xs)
  rewrite merge-split {A} m k xs
  = refl

Tᵣ-++ :
  ∀ (m k : Nat) (c : Vec Trit m) (t : Vec Trit k) →
  Tᵣ {m} {k} (c ++ t) ≡ c ++ tailStep t
Tᵣ-++ m k c t
  rewrite Rᵣ-++ m k c t
        | Pᵣ-++ m k c (shiftTail t)
  = refl

split-Tᵣ :
  ∀ (m k : Nat) (x : Vec Trit (m + k)) →
  split m k (Tᵣ {m} {k} x) ≡ (coarseOf m k x , tailStep (tailOf m k x))
split-Tᵣ m k x with split m k x
... | (c , t)
  rewrite Rᵣ-++ m k c t
        | Pᵣ-++ m k c (shiftTail t)
        | split-++ m k c (projTail (shiftTail t))
  = refl

split-iterate-Tᵣ :
  ∀ (m k n : Nat) (x : Vec Trit (m + k)) →
  split m k (iterate n (Tᵣ {m} {k}) x) ≡
    ( coarseOf m k x
    , iterate n tailStep (tailOf m k x)
    )
split-iterate-Tᵣ m k zero x
  = sym (pair-η (split m k x))
split-iterate-Tᵣ m k (suc n) x
  rewrite split-iterate-Tᵣ m k n (Tᵣ {m} {k} x)
        | split-Tᵣ m k x
  = refl

tailOf-after-Tk :
  ∀ (m k : Nat) (x : Vec Trit (m + k)) →
  tailOf m k (iterate k (Tᵣ {m} {k}) x) ≡ replicate k zer
tailOf-after-Tk m k x =
  trans
    (cong proj₂ (split-iterate-Tᵣ m k k x))
    (tailCollapse k (tailOf m k x))
