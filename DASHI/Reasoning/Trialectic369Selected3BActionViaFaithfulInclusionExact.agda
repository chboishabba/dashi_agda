module DASHI.Reasoning.Trialectic369Selected3BActionViaFaithfulInclusionExact where

------------------------------------------------------------------------
-- SAME-OBJECT SOURCE ACTION: TEST AT THE ACTUAL CONSTITUENT INCLUSION.
--
-- The existing weight-two source already supplies the constituent action and
-- inclusion into the full grade-two linear carrier. It remains to compare the
-- selected normalizer action on this SAME constituent.
--
-- An injective inclusion lets one discharge that comparison in the full
-- grade-two carrier. No character/dimension/finite index argument is used.
-- The two receipts below are genuine source obligations, not supplied here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong; sym; trans; subst)

import DASHI.Geometry.HilbertLorentzForcing as Linear
import DASHI.Moonshine.MonsterWeightTwoLinearActionBridgeExact as WeightTwo
import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as Inertia
import DASHI.Moonshine.Base369Monster3BSingleActionProducerBidiExact as Single
import DASHI.Reasoning.Trialectic369CanonicalSelected3BLinearCoreExact as Core

transportBack :
  ∀ {A B : Set} → A ≡ B → B → A
transportBack equality = subst (λ T → T) (sym equality)

transportForward :
  ∀ {A B : Set} → A ≡ B → A → B
transportForward equality = subst (λ T → T) equality

transportBackAfterForward :
  ∀ {A B : Set} (equality : A ≡ B) (x : A) →
  transportBack equality (transportForward equality x) ≡ x
transportBackAfterForward refl x = refl

transportForwardComparison :
  ∀ {A B : Set} (equality : A ≡ B) (x : A) (y : B) →
  x ≡ transportBack equality y →
  transportForward equality x ≡ y
transportForwardComparison refl x y h = h

selectedActionBackOnConstituent :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  Single.Normalizer (Core.linearProducer core) →
  Linear.Vector
    (WeightTwo.constituentLinearCarrier (Core.weightTwoLinearBridge core)) →
  Linear.Vector
    (WeightTwo.constituentLinearCarrier (Core.weightTwoLinearBridge core))
selectedActionBackOnConstituent core normalizer state =
  transportBack
    (Core.constituentCarrierIsSelectedState core)
    (Inertia.act
      (Single.normalizerAction (Core.linearProducer core))
      normalizer
      (transportForward
        (Core.constituentCarrierIsSelectedState core) state))

record FaithfulConstituentActionComparison
    {Monster K : Set}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K})
    : Set₁ where
  field
    inclusionInjective :
      ∀ {left right :
        Linear.Vector
          (WeightTwo.constituentLinearCarrier
            (Core.weightTwoLinearBridge core))} →
      WeightTwo.constituentInclusion (Core.weightTwoLinearBridge core) left
      ≡
      WeightTwo.constituentInclusion (Core.weightTwoLinearBridge core) right
      →
      left ≡ right

    actionsAgreeAfterFullGradeTwoInclusion :
      (normalizer : Single.Normalizer (Core.linearProducer core)) →
      (state :
        Linear.Vector
          (WeightTwo.constituentLinearCarrier
            (Core.weightTwoLinearBridge core))) →
      WeightTwo.constituentInclusion (Core.weightTwoLinearBridge core)
        (WeightTwo.constituentAct (Core.weightTwoLinearBridge core)
          (Core.normalizerToMonster core normalizer) state)
      ≡
      WeightTwo.constituentInclusion (Core.weightTwoLinearBridge core)
        (selectedActionBackOnConstituent core normalizer state)

open FaithfulConstituentActionComparison public

compileActionIntertwiningFromInclusion :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  FaithfulConstituentActionComparison core →
  Core.CanonicalSelected3BActionIntertwining core
compileActionIntertwiningFromInclusion core comparison =
  record { intertwines = λ normalizer state →
    transportForwardComparison
      (Core.constituentCarrierIsSelectedState core)
      (WeightTwo.constituentAct (Core.weightTwoLinearBridge core)
        (Core.normalizerToMonster core normalizer) state)
      (Inertia.act
        (Single.normalizerAction (Core.linearProducer core))
        normalizer
        (transportForward (Core.constituentCarrierIsSelectedState core) state))
      (inclusionInjective comparison
        (actionsAgreeAfterFullGradeTwoInclusion comparison normalizer state))
    }

record IncludedActionCounterexample
    {Monster K : Set}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K})
    : Set₁ where
  field
    normalizer : Single.Normalizer (Core.linearProducer core)
    state :
      Linear.Vector
        (WeightTwo.constituentLinearCarrier
          (Core.weightTwoLinearBridge core))
    selectedActionMismatch :
      WeightTwo.constituentAct (Core.weightTwoLinearBridge core)
        (Core.normalizerToMonster core normalizer) state
      ≢ selectedActionBackOnConstituent core normalizer state

open IncludedActionCounterexample public

counterexampleRejectsActionIntertwining :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  IncludedActionCounterexample core →
  Core.CanonicalSelected3BActionIntertwining core →
  ⊥
counterexampleRejectsActionIntertwining core witness action =
  selectedActionMismatch witness
    (trans
      (sym
        (transportBackAfterForward
          (Core.constituentCarrierIsSelectedState core)
          (WeightTwo.constituentAct (Core.weightTwoLinearBridge core)
            (Core.normalizerToMonster core (normalizer witness))
            (state witness))))
      (cong
        (transportBack (Core.constituentCarrierIsSelectedState core))
        (Core.intertwines action (normalizer witness) (state witness))))

record Boundary : Set where
  constructor boundary
  field
    fullGradeTwoComparisonCriterionOwned : Bool
    injectivityOfConstituentInclusionRequired : Bool
    selectedActionCompilerOwned : Bool
    sourceComparisonWitnessSupplied : Bool
    canonicalCoreInhabitedHere : Bool

canonicalBoundary : Boundary
canonicalBoundary = boundary true true true false false
