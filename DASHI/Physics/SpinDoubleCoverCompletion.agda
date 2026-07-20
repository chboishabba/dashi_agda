module DASHI.Physics.SpinDoubleCoverCompletion where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Sum using (_⊎_)
open import DASHI.Physics.SpinAssumptions as SA
open import DASHI.Physics.CliffordRepresentationCompletion as CRC

record Surjective {A B : Set} (f : A → B) : Set₁ where
  field
    preimage : B → A
    rightInverse : ∀ y → f (preimage y) ≡ y

record TwoPointKernel {A B : Set}
  (GA : SA.Group A) (GB : SA.Group B)
  (h : SA.Hom GA GB) : Set₁ where
  open SA.Group GA
  open SA.Hom h
  field
    minusOne : A
    minusOne≢one : Set
    kernelClassifies : ∀ x → f x ≡ SA.Group.e GB →
      (x ≡ e) ⊎ (x ≡ minusOne)

record SpinDoubleCoverRealization : Set₁ where
  field
    SpinCarrier LorentzCarrier : Set
    spinGroup : SA.Group SpinCarrier
    lorentzGroup : SA.Group LorentzCarrier
    cover : SA.Hom spinGroup lorentzGroup
    onto : Surjective (SA.Hom.f cover)
    kernelTwo : TwoPointKernel spinGroup lorentzGroup cover
    clifford : CRC.CliffordExistence
    conjugationActionCompatible : Set

open SpinDoubleCoverRealization public
