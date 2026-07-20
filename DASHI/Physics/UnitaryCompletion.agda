module DASHI.Physics.UnitaryCompletion where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; _+_)

record InnerProductSpace : Set₁ where
  field
    H Scalar : Set
    zeroH : H
    inner : H → H → Scalar

record Isometry (H : InnerProductSpace) : Set₁ where
  open InnerProductSpace H
  field
    map : H → H
    preservesInner : ∀ x y → inner (map x) (map y) ≡ inner x y

record CompletionData : Set₁ where
  field
    PreHilbert : Set
    completed : InnerProductSpace
    embed : PreHilbert → InnerProductSpace.H completed
    dense : Set

record UnitaryEvolution (C : CompletionData) : Set₁ where
  open CompletionData C
  field
    U : Nat → Isometry completed
    identityTime : ∀ x → Isometry.map (U zero) x ≡ x
    composition : ∀ m n x →
      Isometry.map (U (m + n)) x
        ≡ Isometry.map (U m) (Isometry.map (U n) x)
    support : InnerProductSpace.H completed → Set
    interferencePruning : Set

record UnitaryCompletionClosure : Set₁ where
  field
    completion : CompletionData
    evolution : UnitaryEvolution completion

open UnitaryCompletionClosure public
