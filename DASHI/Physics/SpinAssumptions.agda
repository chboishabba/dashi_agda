module DASHI.Physics.SpinAssumptions where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Unit using (⊤)

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

postulate
  SO   : Nat → Nat → Set
  Spin : Nat → Nat → Set

postulate
  spinGroup : ∀ p q → Group (Spin p q)
  soGroup   : ∀ p q → Group (SO p q)
  spinCoversSO : ∀ (p q : Nat) → DoubleCover (spinGroup p q) (soGroup p q)
