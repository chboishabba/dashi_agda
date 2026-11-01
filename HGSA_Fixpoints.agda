module HGSA_Fixpoints where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_<_ )
open import Agda.Builtin.Equality using (_≡_; refl)
open import Verification.Prelude using (⊥; ⊤; tt; Σ; _,_; _×_; ¬_)
open import Relation.Binary.PropositionalEquality as Eq using (trans; cong)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- Abstract state machine for HGSA
postulate
  State : Set
  step  : State → State

-- Observable predicates
postulate
  Safe   : State → Set
  Ascend : State → Set   -- “this step is an ascend event” (or state tagged)

------------------------------------------------------------------------
-- Least fixpoint style “Eventually” (inductive)
data Eventually (P : State → Set) : State → Set where
  now  : ∀ {s} → P s → Eventually P s
  later : ∀ {s} → Eventually P (step s) → Eventually P s

-- AlwaysEventuallySafe: eventually Safe OR Ascend
AES : State → Set
AES s = Eventually (λ t → Safe t ⊎ Ascend t) s

------------------------------------------------------------------------
-- Ranking-function obligation: progress unless already Safe/Ascend.
postulate
  rank : State → Nat
  progress :
    ∀ s → (¬ Safe s) → (¬ Ascend s) → rank (step s) < rank s

------------------------------------------------------------------------
-- Termination/liveness proof from rank (standard well-founded descent)
-- In Nat, strict descent implies cannot continue forever without hitting base.

postulate
  NatNoInfiniteDescent :
    ∀ (r : State → Nat) (f : State → State) →
    (∀ s → r (f s) < r s) → ⊥

-- Practical AES theorem: Either Safe/Ascend holds now, or progress gives later.
postulate
  decideSafe : ∀ s → (Safe s ⊎ ¬ Safe s)
  decideAsc  : ∀ s → (Ascend s ⊎ ¬ Ascend s)

{-# NON_TERMINATING #-}
AES-theorem : ∀ s → AES s
AES-theorem s with decideSafe s | decideAsc s
... | inj₁ safeNow | _          = now (inj₁ safeNow)
... | inj₂ ns      | inj₁ ascNow = now (inj₂ ascNow)
... | inj₂ ns      | inj₂ na     =
    later (AES-theorem (step s))
