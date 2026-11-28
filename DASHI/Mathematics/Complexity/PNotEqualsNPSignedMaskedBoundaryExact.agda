module DASHI.Mathematics.Complexity.PNotEqualsNPSignedMaskedBoundaryExact where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Agda.Builtin.Equality using (_≡_; refl)

-- The ordered additive carrier can be instantiated by signed integers.
-- This is the semantic seam; native Gaussian/table replay is separate.
module Rules (State Cost : Set)
             (_≤_ : Cost → Cost → Set)
             (_+_ : Cost → Cost → Cost)
             (leTrans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c)
             (addMono : ∀ {a b c d} → a ≤ b → c ≤ d → (a + c) ≤ (b + d))
             where

  record Exact (P : State → Set) (w : State → Cost) : Set where
    constructor exact
    field
      witness : State
      cost : Cost
      feasible : P witness
      attained : w witness ≡ cost
      lower : ∀ z → P z → cost ≤ w z
  open Exact public

  maskedEmpty : ∀ {P Q : State → Set} →
    (∀ z → P z → Q z) → (∀ z → Q z → ⊥) → ∀ z → P z → ⊥
  maskedEmpty mask no z p = no z (mask z p)

  maskedFloor : ∀ {P Q : State → Set} {w : State → Cost} →
    (e : Exact Q w) → (cap : Cost) →
    (∀ z → P z → Q z) → (∀ z → P z → w z ≤ cap) →
    (cost e ≤ cap → ⊥) → ∀ z → P z → ⊥
  maskedFloor e cap mask upper no z p =
    no (leTrans (lower e z (mask z p)) (upper z p))

  chooseLeft : ∀ {P Q : State → Set} {w : State → Cost} →
    (a : Exact P w) → (b : Exact Q w) → cost a ≤ cost b →
    Exact (λ z → P z ⊎ Q z) w
  chooseLeft a b h = exact (witness a) (cost a) (inj₁ (feasible a))
    (attained a) λ { z (inj₁ p) → lower a z p
                   ; z (inj₂ q) → leTrans h (lower b z q) }

  chooseRight : ∀ {P Q : State → Set} {w : State → Cost} →
    (a : Exact P w) → (b : Exact Q w) → cost b ≤ cost a →
    Exact (λ z → P z ⊎ Q z) w
  chooseRight a b h = exact (witness b) (cost b) (inj₂ (feasible b))
    (attained b) λ { z (inj₁ p) → leTrans h (lower a z p)
                   ; z (inj₂ q) → lower b z q }

  joinExact : ∀ {P L R : State → Set} {wl wr : State → Cost} →
    (a : Exact L wl) → (b : Exact R wr) →
    (∀ z → P z → L z × R z) →
    (z : State) → P z → wl z ≡ cost a → wr z ≡ cost b →
    Exact P (λ x → wl x + wr x)
  joinExact a b cover z p ea eb = exact z (cost a + cost b) p
    (sumEq ea eb) (λ x px → addMono (lower a x (proj₁ (cover x px)))
                                     (lower b x (proj₂ (cover x px))))
    where
    sumEq : ∀ {a b c d : Cost} → a ≡ b → c ≡ d → (a + c) ≡ (b + d)
    sumEq refl refl = refl
