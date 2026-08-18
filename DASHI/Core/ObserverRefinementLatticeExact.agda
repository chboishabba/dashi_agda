module DASHI.Core.ObserverRefinementLatticeExact where

open import DASHI.Core.Prelude

Observer : Set → Set → Set
Observer State Value = State → Value

ObservationalEq : ∀ {State Value : Set} → Observer State Value → State → State → Set
ObservationalEq observe x y = observe x ≡ observe y

ObservationFibre : ∀ {State Value : Set} → Observer State Value → Value → Set
ObservationFibre {State} observe value = Σ State (λ x → observe x ≡ value)

Separating : ∀ {State Value : Set} → Observer State Value → Set
Separating observe = ∀ x y → observe x ≡ observe y → x ≡ y

Refines : ∀ {State Coarse Fine : Set} → Observer State Coarse → Observer State Fine → Set
Refines coarse fine = ∀ x y → fine x ≡ fine y → coarse x ≡ coarse y

record StrictRefinement {State Coarse Fine : Set}
    (coarse : Observer State Coarse) (fine : Observer State Fine) : Set where
  constructor strictRefinement
  field
    refines : Refines coarse fine
    left right : State
    coarseCollision : coarse left ≡ coarse right
    fineSeparates : fine left ≡ fine right → ⊥
open StrictRefinement public

ObserverFamily : Set → Set → Set
ObserverFamily State Value = List (Observer State Value)

AgreeOn : ∀ {State Value : Set} → ObserverFamily State Value → State → State → Set
AgreeOn [] x y = ⊤
AgreeOn (observe ∷ family) x y = observe x ≡ observe y × AgreeOn family x y

familySelfAgreement : ∀ {State Value : Set} (family : ObserverFamily State Value) (x : State) → AgreeOn family x x
familySelfAgreement [] x = tt
familySelfAgreement (observe ∷ family) x = refl , familySelfAgreement family x

SeparatingFamily : ∀ {State Value : Set} → ObserverFamily State Value → Set
SeparatingFamily family = ∀ x y → AgreeOn family x y → x ≡ y

ResidualObservationFibre : ∀ {State Value : Set} → ObserverFamily State Value → State → Set
ResidualObservationFibre {State} family x = Σ State (λ y → AgreeOn family x y)

FamilyRefines : ∀ {State Value : Set} → ObserverFamily State Value → ObserverFamily State Value → Set
FamilyRefines coarse fine = ∀ x y → AgreeOn fine x y → AgreeOn coarse x y

prependFamilyRefinesTail : ∀ {State Value : Set} (observe : Observer State Value) (family : ObserverFamily State Value) → FamilyRefines family (observe ∷ family)
prependFamilyRefinesTail observe family x y agreement = proj₂ agreement

addingObserverShrinksResidualFibre : ∀ {State Value : Set} (observe : Observer State Value) (family : ObserverFamily State Value) (x : State) → ResidualObservationFibre (observe ∷ family) x → ResidualObservationFibre family x
addingObserverShrinksResidualFibre observe family x point = proj₁ point , proj₂ (proj₂ point)

record StrictFamilyRefinement {State Value : Set}
    (coarse fine : ObserverFamily State Value) : Set where
  constructor strictFamilyRefinement
  field
    familyRefines : FamilyRefines coarse fine
    left right : State
    coarseCollision : AgreeOn coarse left right
    fineSeparates : AgreeOn fine left right → ⊥
open StrictFamilyRefinement public

strictFamilyRefinementBlocksCoarseSeparation : ∀ {State Value : Set} {coarse fine : ObserverFamily State Value} → StrictFamilyRefinement coarse fine → SeparatingFamily coarse → ⊥
strictFamilyRefinementBlocksCoarseSeparation {fine = fine} refinement separating
  with separating (left refinement) (right refinement) (coarseCollision refinement)
... | refl = fineSeparates refinement (familySelfAgreement fine (left refinement))

pairObserver : ∀ {State A B : Set} → Observer State A → Observer State B → Observer State (A × B)
pairObserver left right x = left x , right x

pairRefinesLeft : ∀ {State A B : Set} (left : Observer State A) (right : Observer State B) → Refines left (pairObserver left right)
pairRefinesLeft left right x y equality = cong proj₁ equality

pairRefinesRight : ∀ {State A B : Set} (left : Observer State A) (right : Observer State B) → Refines right (pairObserver left right)
pairRefinesRight left right x y equality = cong proj₂ equality

strictPairRefinement : ∀ {State A B : Set} (coarse : Observer State A) (extra : Observer State B) (x y : State) → coarse x ≡ coarse y → (extra x ≡ extra y → ⊥) → StrictRefinement coarse (pairObserver coarse extra)
strictPairRefinement coarse extra x y coarseSame extraDiff = strictRefinement (pairRefinesLeft coarse extra) x y coarseSame (λ pairSame → extraDiff (cong proj₂ pairSame))

record ObserverCollision {State Value : Set} (observe : Observer State Value) : Set where
  constructor observerCollision
  field
    left right : State
    sameObservation : observe left ≡ observe right
    distinctStates : left ≡ right → ⊥
open ObserverCollision public

collisionBlocksSeparation : ∀ {State Value : Set} {observe : Observer State Value} → ObserverCollision observe → Separating observe → ⊥
collisionBlocksSeparation collision separating = distinctStates collision (separating (left collision) (right collision) (sameObservation collision))

record ObserverRefinementBoundary : Set where
  constructor observerRefinementBoundary
  field
    addingObserversMonotonicallyShrinksResidualFibre : Bool
    addingObserversMonotonicallyShrinksResidualFibreIsTrue : addingObserversMonotonicallyShrinksResidualFibre ≡ true
    refinementAutomaticallySeparating : Bool
    refinementAutomaticallySeparatingIsFalse : refinementAutomaticallySeparating ≡ false
    collisionBlocksSeparationConstructed : Bool
    collisionBlocksSeparationConstructedIsTrue : collisionBlocksSeparationConstructed ≡ true

canonicalObserverRefinementBoundary : ObserverRefinementBoundary
canonicalObserverRefinementBoundary = observerRefinementBoundary true refl false refl true refl
