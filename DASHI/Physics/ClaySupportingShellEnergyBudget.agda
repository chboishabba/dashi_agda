module DASHI.Physics.ClaySupportingShellEnergyBudget where

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; m≤n⇒m≤o+n; m≤n⇒m≤n+o)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

≤-addL : (a b : Nat) → a ≤ a + b
≤-addL a b = m≤n⇒m≤n+o b ≤-refl

≤-addR : (a b : Nat) → b ≤ a + b
≤-addR a b = m≤n⇒m≤o+n a ≤-refl

≤-split : (k n : Nat) → k ≤ n → (k ≡ n) ⊎ (suc k ≤ n)
≤-split zero zero z≤n = inj₁ refl
≤-split zero (suc n) z≤n = inj₂ (s≤s z≤n)
≤-split (suc k) (suc n) (s≤s k≤n) with ≤-split k n k≤n
... | inj₁ refl = inj₁ refl
... | inj₂ sk≤n = inj₂ (s≤s sk≤n)

sum : (Nat → Nat) → Nat → Nat
sum f zero = f zero
sum f (suc n) = f (suc n) + sum f n

sumDomination : (f : Nat → Nat) → (n k : Nat) → (k ≤ n) → f k ≤ sum f n
sumDomination f zero zero z≤n = ≤-refl
sumDomination f (suc n) k k≤suc-n with ≤-split k (suc n) k≤suc-n
... | inj₁ refl = ≤-addL (f (suc n)) (sum f n)
... | inj₂ (s≤s k≤n) =
  ≤-trans (sumDomination f n k k≤n) (≤-addR (f (suc n)) (sum f n))

shellBudgetFromGlobalDissipation :
  (shellBudget : Nat → Nat) →
  (R N : Nat) →
  (N ≤ R) →
  (C : Nat) →
  (globalBudget : Nat) →
  (sumBound : sum shellBudget R ≤ C * globalBudget) →
  shellBudget N ≤ C * globalBudget
shellBudgetFromGlobalDissipation shellBudget R N N≤R C globalBudget sumBound =
  let
    dom : shellBudget N ≤ sum shellBudget R
    dom = sumDomination shellBudget R N N≤R
  in
  ≤-trans dom sumBound
