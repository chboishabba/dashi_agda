module DASHI.Physics.SpinAssumptions where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Unit using (⊤; tt)

record Group (G : Set) : Set₁ where
  field
    e   : G
    _∙_ : G → G → G
    inv : G → G

record Hom {G H : Set} (GG : Group G) (HH : Group H) : Set₁ where
  open Group GG renaming (_∙_ to _∙G_; e to eG; inv to invG)
  open Group HH renaming (_∙_ to _∙H_; e to eH; inv to invH)
  field
    f     : G → H
    pres∙ : ∀ x y → f (x ∙G y) ≡ f x ∙H f y
    prese : f eG ≡ eH

record DoubleCover {G H : Set} (GG : Group G) (HH : Group H) : Set₁ where
  field
    ρ     : Hom GG HH
    surj  : ⊤
    twoTo1 : ⊤

record SpinAxioms : Set₁ where
  field
    SO   : Nat → Nat → Set
    Spin : Nat → Nat → Set

    spinGroup : ∀ p q → Group (Spin p q)
    soGroup   : ∀ p q → Group (SO p q)
    spinCoversSO : ∀ (p q : Nat) → DoubleCover (spinGroup p q) (soGroup p q)

SO : SpinAxioms → Nat → Nat → Set
SO A = SpinAxioms.SO A

Spin : SpinAxioms → Nat → Nat → Set
Spin A = SpinAxioms.Spin A

spinGroup : (A : SpinAxioms) → ∀ p q → Group (Spin A p q)
spinGroup A = SpinAxioms.spinGroup A

soGroup : (A : SpinAxioms) → ∀ p q → Group (SO A p q)
soGroup A = SpinAxioms.soGroup A

spinCoversSO : (A : SpinAxioms) → ∀ (p q : Nat) → DoubleCover (spinGroup A p q) (soGroup A p q)
spinCoversSO A = SpinAxioms.spinCoversSO A

-- Default instance (data-level placeholder).
spinAxiomsDefault : SpinAxioms
spinAxiomsDefault =
  record
    { SO = λ _ _ → ⊤
    ; Spin = λ _ _ → ⊤
    ; spinGroup = λ _ _ →
        record { e = tt ; _∙_ = λ _ _ → tt ; inv = λ _ → tt }
    ; soGroup = λ _ _ →
        record { e = tt ; _∙_ = λ _ _ → tt ; inv = λ _ → tt }
    ; spinCoversSO = λ _ _ →
        record
          { ρ = record
              { f = λ _ → tt
              ; pres∙ = λ _ _ → refl
              ; prese = refl
              }
          ; surj = tt
          ; twoTo1 = tt
          }
    }
