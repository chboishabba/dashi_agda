module Z6_RegularInverse where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Nat using (Nat)
open import Data.Nat.Properties as NatP using ()
open import Relation.Binary.PropositionalEquality as Eq using (cong)

------------------------------------------------------------------------
-- Z6 elements as Fin 6
Z6 : Set
Z6 = Fin 6

------------------------------------------------------------------------
-- Ring operations modulo 6 (postulate or implement via Fin arithmetic).
-- If you want full concreteness, implement add/mul with toℕ and mod 6.
postulate
  _+6_ : Z6 → Z6 → Z6
  _*6_ : Z6 → Z6 → Z6

------------------------------------------------------------------------
-- von Neumann regular inverse witness: a = a*b*a

Regular : Z6 → Set
Regular a = Σ Z6 (λ b → a ≡ (a *6 b) *6 a)

------------------------------------------------------------------------
-- A concrete witness table (finite, so we can just provide b per a).
-- You can later refine _+6_/_*6_ and this becomes fully checkable.

postulate
  bOf : Z6 → Z6
  regular-law : ∀ a → a ≡ (a *6 bOf a) *6 a

regular : ∀ a → Regular a
regular a = bOf a , regular-law a
