module DASHI.Physics.Refinement where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.PhysicalTheory as PT

record RefinementStep {ℓ : Level}
  (T₀ T₁ : PT.PhysicalTheory ℓ) : Set (lsuc ℓ) where
  open PT.PhysicalTheory T₀ renaming (State to State₀ ; step to step₀ ; Inv to Inv₀)
  open PT.PhysicalTheory T₁ renaming (State to State₁ ; step to step₁ ; Inv to Inv₁)
  field
    project   : State₁ → State₀
    embed     : State₀ → State₁

    project-inv : ∀ {x} → Inv₁ x → Inv₀ (project x)
    embed-inv   : ∀ {x} → Inv₀ x → Inv₁ (embed x)

    commute-project :
      ∀ {x} → Inv₁ x → project (step₁ x) ≡ step₀ (project x)

record ApproxRefinementStep {ℓ : Level}
  (T₀ T₁ : PT.PhysicalTheory ℓ) : Set (lsuc ℓ) where
  open PT.PhysicalTheory T₀ renaming (State to State₀ ; step to step₀)
  open PT.PhysicalTheory T₁ renaming (State to State₁ ; step to step₁)
  field
    project   : State₁ → State₀
    embed     : State₀ → State₁

    approxEq₀ : State₀ → State₀ → Set ℓ

    commute-project≈ :
      ∀ x → approxEq₀ (project (step₁ x)) (step₀ (project x))

record RefinementTower (ℓ : Level) : Set (lsuc ℓ) where
  field
    TheoryAt : Nat → PT.PhysicalTheory ℓ
    refine   : ∀ n → ApproxRefinementStep (TheoryAt n) (TheoryAt (suc n))

record TowerObservable {ℓ : Level}
  (R : RefinementTower ℓ) : Set (lsuc ℓ) where
  open RefinementTower R
  field
    Obs   : ∀ n → PT.State (TheoryAt n) → Set ℓ
    ObsEq : ∀ n → Set ℓ → Set ℓ → Set ℓ

    transport :
      ∀ n x →
      ObsEq n
        (Obs n (ApproxRefinementStep.project (refine n) x))
        (Obs (suc n) x)
