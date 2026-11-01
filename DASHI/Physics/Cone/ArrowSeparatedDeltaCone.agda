module DASHI.Physics.Cone.ArrowSeparatedDeltaCone where

open import Level using (Level; _⊔_; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

-- Abstract split of state into (shape, arrow)
record ArrowSplit {ℓs ℓa ℓx : Level} : Set (suc (ℓs ⊔ ℓa ⊔ ℓx)) where
  field
    State : Set ℓx
    Shape : Set ℓs
    Arrow : Set ℓa
    split : State → Shape × Arrow

open ArrowSplit public

-- Difference operations for shape and arrow components.
record ArrowDelta {ℓs ℓa : Level} (Shape : Set ℓs) (Arrow : Set ℓa)
  : Set (suc (ℓs ⊔ ℓa)) where
  field
    ΔShape : Shape → Shape → Shape
    ΔArrow : Arrow → Arrow → Arrow

open ArrowDelta public

-- Forwardness predicate is only about arrow deltas.
record ForwardPred {ℓa : Level} (Arrow : Set ℓa) : Set (suc ℓa) where
  field
    Forward : Arrow → Set ℓa

open ForwardPred public

-- Cone screen only depends on shape deltas.
record ConeScreen {ℓs : Level} (Shape : Set ℓs) : Set (suc ℓs) where
  field
    Cone : Shape → Set ℓs

open ConeScreen public

-- Derived step predicates.
ForwardStep :
  ∀ {ℓs ℓa ℓx}
  (S : ArrowSplit {ℓs} {ℓa} {ℓx})
  (D : ArrowDelta (Shape S) (Arrow S))
  (F : ForwardPred (Arrow S))
  → State S → State S → Set ℓa
ForwardStep S D F x x' =
  Forward F (ΔArrow D (proj₂ (split S x')) (proj₂ (split S x)))

ConeStep :
  ∀ {ℓs ℓa ℓx}
  (S : ArrowSplit {ℓs} {ℓa} {ℓx})
  (D : ArrowDelta (Shape S) (Arrow S))
  (C : ConeScreen (Shape S))
  → State S → State S → Set ℓs
ConeStep S D C x x' =
  Cone C (ΔShape D (proj₁ (split S x')) (proj₁ (split S x)))

-- Keystone lemma: forward step implies cone screen on shape delta.
record ArrowSeparatedDeltaCone
  {ℓs ℓa ℓx}
  (S : ArrowSplit {ℓs} {ℓa} {ℓx})
  (D : ArrowDelta (Shape S) (Arrow S))
  (F : ForwardPred (Arrow S))
  (C : ConeScreen (Shape S))
  (Step : State S → State S → Set)
  : Set (suc (ℓs ⊔ ℓa ⊔ ℓx)) where
  field
    step⇒forward : ∀ {x x'} → Step x x' → ForwardStep S D F x x'
    forward⇒cone : ∀ {x x'} → Step x x' → ForwardStep S D F x x' → ConeStep S D C x x'

open ArrowSeparatedDeltaCone public

-- Convenience: cone-compatibility predicate on steps.
ConeCompatibleStep :
  ∀ {ℓs ℓa ℓx}
  (S : ArrowSplit {ℓs} {ℓa} {ℓx})
  (D : ArrowDelta (Shape S) (Arrow S))
  (F : ForwardPred (Arrow S))
  (C : ConeScreen (Shape S))
  → State S → State S → Set (ℓs ⊔ ℓa)
ConeCompatibleStep S D F C x x' = ForwardStep S D F x x' → ConeStep S D C x x'

coneCompatibleFromKit :
  ∀ {ℓs ℓa ℓx}
  {S : ArrowSplit {ℓs} {ℓa} {ℓx}}
  {D : ArrowDelta (Shape S) (Arrow S)}
  {F : ForwardPred (Arrow S)}
  {C : ConeScreen (Shape S)}
  {Step : State S → State S → Set}
  → ArrowSeparatedDeltaCone S D F C Step
  → ∀ {x x'} → Step x x' → ConeCompatibleStep S D F C x x'
coneCompatibleFromKit kit st fw = forward⇒cone kit st fw
