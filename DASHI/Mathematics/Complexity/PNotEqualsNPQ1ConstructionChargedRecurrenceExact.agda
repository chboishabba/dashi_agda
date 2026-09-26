module DASHI.Mathematics.Complexity.PNotEqualsNPQ1ConstructionChargedRecurrenceExact where

------------------------------------------------------------------------
-- Q1 DIRECT RESOURCE CUT: CHARGE THE CONSTRUCTOR ITSELF
--
-- The live per-state Q1 witness already proves that the COMPILED authority,
-- quotation overhead, and rebinding overhead are strictly smaller than the
-- current formula/state measure.
--
-- One resource hole remained: an existential closed quotient could in
-- principle be constructed by an exponentially expensive SAT computation and
-- then handed to the cheap downstream recurrence.
--
-- This owner closes that hole.
--
-- A constructive Q1 step must now pay:
--
--   constructionCost + measure(nextState) < measure(currentState).
--
-- Thus the work needed to build the quotient / representatives / structural
-- chains is charged in the SAME well-founded currency as the recursive state.
--
-- We also test the canonical exact finite SAT truth-classifier construction.
-- Its structural recursion has exactly 2^n leaves.  Therefore whenever that
-- cost alone reaches the current recursive measure, it cannot inhabit a
-- construction-charged Q1 step.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as NatP
open import Data.Product using (Σ; _,_; proj₁; proj₂)

import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableStateRecurrenceExact as Recurrence
import DASHI.Mathematics.Complexity.PNotEqualsNPSATTruthQuotientConstructionCostExact as TruthCost

------------------------------------------------------------------------
-- The actual next state encoded by an ordinary Q1 witness.
------------------------------------------------------------------------

q1WitnessNextState :
  (state : Q2.BoundedSelfReferenceState) →
  Recurrence.Q1StateWitness state →
  Q2.BoundedSelfReferenceState
q1WitnessNextState state witness =
  Recurrence.q1AuthorityNextState
    state
    (proj₁ witness)
    (proj₂ witness)

------------------------------------------------------------------------
-- Construction-charged Q1 witness.
------------------------------------------------------------------------

record ConstructionChargedQ1StateWitness
    (state : Q2.BoundedSelfReferenceState) : Set₁ where
  constructor construction-charged-q1-state-witness
  field
    q1Witness :
      Recurrence.Q1StateWitness state

    constructionCost :
      Nat

    constructionAndNextStrict :
      constructionCost
        + Q2.recursiveMeasure
            (q1WitnessNextState state q1Witness)
      <
      Q2.recursiveMeasure state

open ConstructionChargedQ1StateWitness public

ConstructionChargedQ1StateConstructor : Set₁
ConstructionChargedQ1StateConstructor =
  (state : Q2.BoundedSelfReferenceState) →
  Maybe (ConstructionChargedQ1StateWitness state)

------------------------------------------------------------------------
-- Forgetting the charged receipt gives the already-proved Q1 recurrence.
------------------------------------------------------------------------

forgetChargedQ1 :
  ConstructionChargedQ1StateConstructor →
  Recurrence.Q1StateConstructor
forgetChargedQ1 constructor state
    with constructor state
... | nothing =
  nothing
... | just charged =
  just (q1Witness charged)

chargedQ1ConstructorToQ2StepSystem :
  ConstructionChargedQ1StateConstructor →
  Q2.BoundedSelfReferenceStepSystem
chargedQ1ConstructorToQ2StepSystem constructor =
  Recurrence.q1ConstructorToQ2StepSystem
    (forgetChargedQ1 constructor)

------------------------------------------------------------------------
-- The charged witness is strictly stronger than bare Q1 descent.
------------------------------------------------------------------------

chargedQ1StillStrictlyDecreases :
  (state : Q2.BoundedSelfReferenceState) →
  (charged : ConstructionChargedQ1StateWitness state) →
  Q2.recursiveMeasure
      (q1WitnessNextState state (q1Witness charged))
  <
  Q2.recursiveMeasure state
chargedQ1StillStrictlyDecreases state charged =
  NatP.≤-<-trans
    (NatP.m≤m+n
      (Q2.recursiveMeasure
        (q1WitnessNextState state (q1Witness charged)))
      (constructionCost charged))
    reordered
  where
    reordered :
      Q2.recursiveMeasure
          (q1WitnessNextState state (q1Witness charged))
        + constructionCost charged
      <
      Q2.recursiveMeasure state
    reordered
      rewrite NatP.+-comm
        (Q2.recursiveMeasure
          (q1WitnessNextState state (q1Witness charged)))
        (constructionCost charged) =
      constructionAndNextStrict charged

------------------------------------------------------------------------
-- Exact cost of the canonical finite SAT truth-classifier on the current root.
------------------------------------------------------------------------

truthClassifierConstructionCost :
  Q2.BoundedSelfReferenceState →
  Nat
truthClassifierConstructionCost state =
  TruthCost.truthClassifierLeaves
    (Bridge.cookToIndexed
      (Q2.currentFormula state))

truthClassifierConstructionCostExact :
  (state : Q2.BoundedSelfReferenceState) →
  truthClassifierConstructionCost state
  ≡
  TruthCost.pow2
    (Bridge.formulaVariableBound
      (Q2.currentFormula state))
truthClassifierConstructionCostExact state =
  TruthCost.truthClassifierLeavesExact
    (Bridge.cookToIndexed
      (Q2.currentFormula state))

------------------------------------------------------------------------
-- Direct no-go for hiding the exact SAT recursion inside Q1 construction.
------------------------------------------------------------------------

constructionCostAtLeastCurrentMeasureImpossible :
  (state : Q2.BoundedSelfReferenceState) →
  (charged : ConstructionChargedQ1StateWitness state) →
  Q2.recursiveMeasure state
    ≤ constructionCost charged →
  ⊥
constructionCostAtLeastCurrentMeasureImpossible
    state
    charged
    currentBelowCost =
  NatP.<-irrefl
    (Q2.recursiveMeasure state)
    (NatP.≤-<-trans
      currentBelowCostPlusNext
      (constructionAndNextStrict charged))
  where
    costBelowCostPlusNext :
      constructionCost charged
      ≤
      constructionCost charged
        + Q2.recursiveMeasure
            (q1WitnessNextState state (q1Witness charged))
    costBelowCostPlusNext =
      NatP.m≤m+n
        (constructionCost charged)
        (Q2.recursiveMeasure
          (q1WitnessNextState state (q1Witness charged)))

    currentBelowCostPlusNext :
      Q2.recursiveMeasure state
      ≤
      constructionCost charged
        + Q2.recursiveMeasure
            (q1WitnessNextState state (q1Witness charged))
    currentBelowCostPlusNext =
      NatP.≤-trans
        currentBelowCost
        costBelowCostPlusNext

truthClassifierCostCannotBeChargedWhenItReachesCurrentMeasure :
  (state : Q2.BoundedSelfReferenceState) →
  (charged : ConstructionChargedQ1StateWitness state) →
  constructionCost charged
    ≡ truthClassifierConstructionCost state →
  Q2.recursiveMeasure state
    ≤ truthClassifierConstructionCost state →
  ⊥
truthClassifierCostCannotBeChargedWhenItReachesCurrentMeasure
    state
    charged
    costIsTruthClassifier
    currentBelowTruthCost =
  constructionCostAtLeastCurrentMeasureImpossible
    state
    charged
    (NatP.≤-trans
      currentBelowTruthCost
      (NatP.≤-reflexive
        (sym costIsTruthClassifier)))
  where
    sym :
      ∀ {a b : Nat} →
      a ≡ b →
      b ≡ a
    sym refl = refl

------------------------------------------------------------------------
-- Exponential specialization.
------------------------------------------------------------------------

pow2AtLeastCurrentMeasureBlocksExactTruthClassifier :
  (state : Q2.BoundedSelfReferenceState) →
  (charged : ConstructionChargedQ1StateWitness state) →
  constructionCost charged
    ≡ truthClassifierConstructionCost state →
  Q2.recursiveMeasure state
    ≤
    TruthCost.pow2
      (Bridge.formulaVariableBound
        (Q2.currentFormula state)) →
  ⊥
pow2AtLeastCurrentMeasureBlocksExactTruthClassifier
    state
    charged
    costIsTruthClassifier
    currentBelowPow2
    rewrite
      sym
        (truthClassifierConstructionCostExact state) =
  truthClassifierCostCannotBeChargedWhenItReachesCurrentMeasure
    state
    charged
    costIsTruthClassifier
    currentBelowPow2
  where
    sym :
      ∀ {a b : Nat} →
      a ≡ b →
      b ≡ a
    sym refl = refl

------------------------------------------------------------------------
-- CLAY CONSEQUENCE
--
-- The direct Q1 target is now stronger and honest:
--
--   construct, SAT-blindly, at every live state:
--
--     closed quotient
--     + all-overhead authority descent
--     + an explicit construction cost
--     + constructionCost + measure(next) < measure(current).
--
-- The canonical exact SAT recursion is ruled out whenever its exact 2^n leaf
-- cost already reaches the current measure.  Hence a successful Q1 mechanism
-- must obtain the special quotient/chains intensionally, with genuine resource
-- savings during CONSTRUCTION rather than only after construction.
------------------------------------------------------------------------
