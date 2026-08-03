module DASHI.Physics.Limits.PhysicsLimitCommutingSquare where

------------------------------------------------------------------------
-- PURPOSE
-- A reusable theory-translation spine.  Exact unification means path
-- independence.  Effective or limiting recovery must instead own a residual
-- and a theorem that controls or removes it.  Merely naming both paths is not a
-- commuting-square proof.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

record TheoryPresentation
    {stateLevel equationLevel observableLevel scaleLevel : Level}
    : Set (lsuc (stateLevel ⊔ equationLevel ⊔ observableLevel ⊔ scaleLevel)) where
  field
    State : Set stateLevel
    Equation : Set equationLevel
    Observable : Set observableLevel
    ScaleRegime : Set scaleLevel

open TheoryPresentation public

record TheoryTranslation
    {s₁ e₁ o₁ r₁ s₂ e₂ o₂ r₂ : Level}
    (source : TheoryPresentation {s₁} {e₁} {o₁} {r₁})
    (target : TheoryPresentation {s₂} {e₂} {o₂} {r₂})
    : Set (lsuc (s₁ ⊔ e₁ ⊔ o₁ ⊔ r₁ ⊔ s₂ ⊔ e₂ ⊔ o₂ ⊔ r₂)) where
  field
    mapState : State source → State target
    mapEquation : Equation source → Equation target
    mapObservable : Observable source → Observable target
    mapScale : ScaleRegime source → ScaleRegime target

open TheoryTranslation public

record CommutingSquare
    {a b c d : Level}
    (A : Set a) (B : Set b) (C : Set c) (D : Set d)
    : Set (lsuc (a ⊔ b ⊔ c ⊔ d)) where
  field
    top : A → B
    left : A → C
    right : B → D
    bottom : C → D

open CommutingSquare public

record ExactCommutation
    {a b c d : Level}
    {A : Set a} {B : Set b} {C : Set c} {D : Set d}
    (square : CommutingSquare A B C D)
    : Set (a ⊔ d) where
  field
    pathsAgree :
      (input : A) →
      right square (top square input)
      ≡ bottom square (left square input)

open ExactCommutation public

pathIndependence :
  ∀ {a b c d}
    {A : Set a} {B : Set b} {C : Set c} {D : Set d}
    {square : CommutingSquare A B C D} →
  ExactCommutation square →
  (input : A) →
  right square (top square input)
  ≡ bottom square (left square input)
pathIndependence exact = pathsAgree exact

record ResidualControlledCommutation
    {a b c d residualLevel : Level}
    {A : Set a} {B : Set b} {C : Set c} {D : Set d}
    (square : CommutingSquare A B C D)
    (Residual : Set residualLevel)
    : Set (lsuc (a ⊔ d ⊔ residualLevel)) where
  field
    residual : A → Residual
    discrepancy : D → D → Residual
    residualIdentity :
      (input : A) →
      discrepancy
        (right square (top square input))
        (bottom square (left square input))
      ≡ residual input

    Controlled : Residual → Set residualLevel
    controlled : (input : A) → Controlled (residual input)

open ResidualControlledCommutation public

record AsymptoticCommutation
    {a b c d residualLevel : Level}
    {A : Set a} {B : Set b} {C : Set c} {D : Set d}
    (square : CommutingSquare A B C D)
    (Residual : Set residualLevel)
    : Set (lsuc (a ⊔ d ⊔ residualLevel)) where
  field
    approximation :
      ResidualControlledCommutation square Residual

    zeroResidual : Residual
    residualAtScale : Nat → A → Residual

    residualAtScaleMeaning :
      (scale : Nat) →
      (input : A) →
      residualAtScale scale input
      ≡ ResidualControlledCommutation.residual approximation input

    Vanishes : (Nat → Residual) → Set residualLevel
    residualVanishes :
      (input : A) → Vanishes (λ scale → residualAtScale scale input)

open AsymptoticCommutation public

record PromotionDiscipline : Set₁ where
  field
    exactEquivalenceRequiresExactCommutation : Set
    effectiveTheoryRequiresControlledResidual : Set
    asymptoticRecoveryRequiresVanishingResidual : Set
    uncontrolledResidualBlocksPromotion : Set

open PromotionDiscipline public
