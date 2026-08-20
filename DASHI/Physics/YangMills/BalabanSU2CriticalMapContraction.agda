module DASHI.Physics.YangMills.BalabanSU2CriticalMapContraction where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; trans)

_≢_ : ∀ {a} {A : Set a} → A → A → Set a
x ≢ y = x ≡ y → ⊥

record FiniteCriticalContraction
  {s d : Level}
  (State : Set s)
  (Distance : Set d) : Set (s ⊔ d) where
  field
    step : State → State
    distance : State → State → Distance
    StrictlySmaller : Distance → Distance → Set d
    strictIrreflexive : ∀ value → StrictlySmaller value value → ⊥
    distinctOrEqual : ∀ left right → left ≡ right ⊎ left ≢ right
    fixedPoint : State
    fixed : step fixedPoint ≡ fixedPoint
    contractiveOnDistinct :
      ∀ {left right} → left ≢ right →
      StrictlySmaller
        (distance (step left) (step right))
        (distance left right)

open FiniteCriticalContraction public

fixedPointUnique :
  ∀ {s d} {State : Set s} {Distance : Set d}
  (bundle : FiniteCriticalContraction State Distance) →
  ∀ state → step bundle state ≡ state → state ≡ fixedPoint bundle
fixedPointUnique bundle state stateFixed
  with distinctOrEqual bundle state (fixedPoint bundle)
... | inj₁ equal = equal
... | inj₂ distinct =
  let
    decrease = contractiveOnDistinct bundle distinct
    sameDistance =
      trans
        (cong (λ left → distance bundle left (step bundle (fixedPoint bundle))) stateFixed)
        (cong (distance bundle state) (fixed bundle))
  in
  ⊥-elim
    (strictIrreflexive bundle (distance bundle state (fixedPoint bundle))
      (substSmaller bundle sameDistance decrease))
  where
    ⊥-elim : ⊥ → state ≡ fixedPoint bundle
    ⊥-elim ()

    substSmaller :
      ∀ {s d} {State : Set s} {Distance : Set d}
      (dataSet : FiniteCriticalContraction State Distance) →
      ∀ {left right target} →
      left ≡ target →
      StrictlySmaller dataSet left right →
      StrictlySmaller dataSet target right
    substSmaller dataSet refl proof = proof
