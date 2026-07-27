module DASHI.Physics.YangMills.BalabanSU2CriticalMapContraction where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; trans)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

record FiniteCriticalContraction
  (State Distance : Set) : Set₁ where
  field
    step : State → State
    distance : State → State → Distance
    StrictlySmaller : Distance → Distance → Set
    strictIrreflexive : ∀ value → StrictlySmaller value value → ⊥
    distinctOrEqual : ∀ (left right : State) → left ≡ right ⊎ left ≢ right
    fixedPoint : State
    fixed : step fixedPoint ≡ fixedPoint
    contractiveOnDistinct :
      ∀ {left right} → left ≢ right →
      StrictlySmaller
        (distance (step left) (step right))
        (distance left right)

open FiniteCriticalContraction public

fixedPointUnique :
  ∀ {State Distance : Set}
  (bundle : FiniteCriticalContraction State Distance) →
  ∀ state → step bundle state ≡ state → state ≡ fixedPoint bundle
fixedPointUnique bundle state stateFixed = helper (distinctOrEqual bundle state (fixedPoint bundle))
  where
    ⊥-elim : ⊥ → state ≡ fixedPoint bundle
    ⊥-elim ()

    substSmaller :
      ∀ {left right target} →
      left ≡ target →
      StrictlySmaller bundle left right →
      StrictlySmaller bundle target right
    substSmaller refl proof = proof

    helper : state ≡ fixedPoint bundle ⊎ state ≢ fixedPoint bundle → state ≡ fixedPoint bundle
    helper (inj₁ equal) = equal
    helper (inj₂ distinct) =
      let
        decrease = contractiveOnDistinct bundle distinct
        sameDistance =
          trans
            (cong (λ left → distance bundle left (step bundle (fixedPoint bundle))) stateFixed)
            (cong (distance bundle state) (fixed bundle))
      in
      ⊥-elim
        (strictIrreflexive bundle (distance bundle state (fixedPoint bundle))
          (substSmaller sameDistance decrease))
