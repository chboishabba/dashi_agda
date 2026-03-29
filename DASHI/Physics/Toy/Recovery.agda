module DASHI.Physics.Toy.Recovery where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_; _<_)

infix 4 _≢_

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

record ToyTheory : Set₁ where
  field
    X            : Set
    Obs          : Set
    RecoveredLaw : Set

    step   : X → X
    defect : X → Nat
    obs    : X → Obs
    inv    : X → Set

    inv-preserved : ∀ {x} → inv x → inv (step x)
    defect-desc   : ∀ {x} → inv x → defect (step x) ≤ defect x
    defect-strict : ∀ {x} → inv x → defect x ≢ zero → defect (step x) < defect x

    stable : X → Set
    stable-fixed : ∀ {x} → stable x → step x ≡ x
    stable-from-zero-defect : ∀ {x} → inv x → defect x ≡ zero → stable x
    recovered-from-stable : ∀ {x} → stable x → RecoveredLaw

open ToyTheory public

record StablePoint (T : ToyTheory) : Set₁ where
  field
    point : X T
    fixed : step T point ≡ point
    law   : RecoveredLaw T

open StablePoint public

record RecoveryAxiom (T : ToyTheory) : Set₁ where
  field
    stable-point : (x₀ : X T) → inv T x₀ → StablePoint T

open RecoveryAxiom public
