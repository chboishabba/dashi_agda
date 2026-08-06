module DASHI.Cognition.PNF.ComplexityArithmetic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

------------------------------------------------------------------------
-- A tiny arithmetic kernel for executable complexity certificates.
-- It is deliberately local so the PNF cost proofs do not depend on an
-- external asymptotics library or on unrecorded machine-cost assumptions.
------------------------------------------------------------------------

infixl 6 _+ᶜ_
infixl 7 _*ᶜ_
infix 4 _≤ᶜ_

_+ᶜ_ : Nat → Nat → Nat
zero +ᶜ n = n
suc m +ᶜ n = suc (m +ᶜ n)

_*ᶜ_ : Nat → Nat → Nat
zero *ᶜ n = zero
suc m *ᶜ n = n +ᶜ (m *ᶜ n)

data _≤ᶜ_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ᶜ n
  s≤s : ∀ {m n} → m ≤ᶜ n → suc m ≤ᶜ suc n

≤ᶜ-refl : ∀ n → n ≤ᶜ n
≤ᶜ-refl zero = z≤n
≤ᶜ-refl (suc n) = s≤s (≤ᶜ-refl n)

≤ᶜ-step : ∀ {m n} → m ≤ᶜ n → m ≤ᶜ suc n
≤ᶜ-step z≤n = z≤n
≤ᶜ-step (s≤s proof) = s≤s (≤ᶜ-step proof)

≤ᶜ-trans : ∀ {a b c} → a ≤ᶜ b → b ≤ᶜ c → a ≤ᶜ c
≤ᶜ-trans z≤n right = z≤n
≤ᶜ-trans (s≤s left) (s≤s right) = s≤s (≤ᶜ-trans left right)

right-summand≤ : ∀ left right → right ≤ᶜ (left +ᶜ right)
right-summand≤ zero right = ≤ᶜ-refl right
right-summand≤ (suc left) right = ≤ᶜ-step (right-summand≤ left right)

+ᶜ-monotone-right : ∀ {a b} → a ≤ᶜ b → ∀ c → (a +ᶜ c) ≤ᶜ (b +ᶜ c)
+ᶜ-monotone-right z≤n c = right-summand≤ _ c
+ᶜ-monotone-right (s≤s proof) c = s≤s (+ᶜ-monotone-right proof c)

+ᶜ-monotone-left : ∀ {a b} → a ≤ᶜ b → ∀ c → (c +ᶜ a) ≤ᶜ (c +ᶜ b)
+ᶜ-monotone-left proof zero = proof
+ᶜ-monotone-left proof (suc c) = s≤s (+ᶜ-monotone-left proof c)

+ᶜ-assoc : ∀ a b c → ((a +ᶜ b) +ᶜ c) ≡ (a +ᶜ (b +ᶜ c))
+ᶜ-assoc zero b c = refl
+ᶜ-assoc (suc a) b c rewrite +ᶜ-assoc a b c = refl

*ᶜ-suc-left : ∀ n m → (suc n *ᶜ m) ≡ (m +ᶜ (n *ᶜ m))
*ᶜ-suc-left n m = refl
