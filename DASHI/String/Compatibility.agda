module DASHI.String.Compatibility where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Relation.Nullary

open import DASHI.String.Unitary
open import DASHI.String.HilbertToy

postulate
  Metric : Set → Set₁
  d      : ∀ {S} → Metric S → S → S → Nat

record Invertible {S : Set} (F : S → S) : Set where
  field
    inv : S → S
    leftInv  : ∀ x → inv (F x) ≡ x
    rightInv : ∀ x → F (inv x) ≡ x

postulate
  StrictContractive :
    ∀ {S} →
    Metric S →
    (S → S) →
    Set

unitary-not-strictly-contractive :
  ∀ {H}
  (Urec : Unitary H)
  (M : Metric (InnerProductSpace.V H)) →
  ¬ StrictContractive M (Unitary.U Urec)
unitary-not-strictly-contractive Urec M = λ sc → ?
