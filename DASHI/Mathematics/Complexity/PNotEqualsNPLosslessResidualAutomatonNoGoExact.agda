module DASHI.Mathematics.Complexity.PNotEqualsNPLosslessResidualAutomatonNoGoExact where

------------------------------------------------------------------------
-- LOSSLESS RAW-RESIDUAL AUTOMATON NO-GO
--
-- Concrete candidate under audit:
--
--   build the quotient state by memoizing the exact local gate-residual vector.
--
-- This is SAT-blind and operationally honest, but the repository already proves
-- that for every concrete Boolean circuit the raw local residual family is the
-- full cube Bool^g.
--
-- Therefore any quotient state which losslessly distinguishes/reopens every raw
-- residual vector needs at least 2^g states.
--
-- Combined with the live operational Q1 theorem
--
--   stateCount(Q) < recursiveMeasure(current),
--
-- this kills the lossless-residual automaton whenever
--
--   recursiveMeasure(current) <= 2^g.
--
-- Hence "memoize exact residual syntax" cannot be the missing compressed Q1
-- builder in precisely the regime where exponential residual width reaches the
-- self-reference budget.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (_≤_; _<_)
open import Data.Product using (Σ; _,_)
import Data.Nat.Properties as NatP
open import Data.Vec.Base using (Vec)

import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableStateRecurrenceExact as Recurrence
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1OperationalConstructionCostExact as Operational
import DASHI.Mathematics.Complexity.PNotEqualsNPExactResidualSummaryBitLowerBoundExact as ResidualBits

------------------------------------------------------------------------
-- Lossless realization of every g-bit raw residual as a quotient state.
--
-- Injectivity is exactly the requirement that the state retains enough
-- information to distinguish all raw residual vectors.  No SAT semantics are
-- assumed here.
------------------------------------------------------------------------

record LosslessResidualStateRealization
    (gates stateCount : Nat) : Set₁ where
  constructor lossless-residual-state-realization
  field
    encode :
      Vec Bool gates →
      Fin stateCount

    encodeInjective :
      ∀ {left right : Vec Bool gates} →
      encode left ≡ encode right →
      left ≡ right

open LosslessResidualStateRealization public

------------------------------------------------------------------------
-- Canonical finite-index encoding of Bool^g into the proposed quotient states.
------------------------------------------------------------------------

residualStateOnFin :
  ∀ {gates stateCount : Nat} →
  LosslessResidualStateRealization gates stateCount →
  Fin (ResidualBits.bitCardinality gates) →
  Fin stateCount
residualStateOnFin realization sourceIndex =
  encode realization
    (ResidualBits.finToBits sourceIndex)

residualStateOnFinInjective :
  ∀ {gates stateCount : Nat}
    (realization :
      LosslessResidualStateRealization gates stateCount)
    {left right :
      Fin (ResidualBits.bitCardinality gates)} →
  residualStateOnFin realization left
  ≡ residualStateOnFin realization right →
  left ≡ right
residualStateOnFinInjective realization same =
  ResidualBits.finToBitsInjective
    (encodeInjective realization same)

------------------------------------------------------------------------
-- Cardinality no-go.
------------------------------------------------------------------------

losslessResidualStatesCannotBeFewerThanCube :
  ∀ {gates stateCount : Nat} →
  stateCount < ResidualBits.bitCardinality gates →
  LosslessResidualStateRealization gates stateCount →
  ⊥
losslessResidualStatesCannotBeFewerThanCube
    tooFew
    realization =
  FinP.<⇒notInjective
    tooFew
    (residualStateOnFinInjective realization)

losslessResidualStatesNeedAtLeastCube :
  ∀ {gates stateCount : Nat} →
  LosslessResidualStateRealization gates stateCount →
  ResidualBits.bitCardinality gates ≤ stateCount
losslessResidualStatesNeedAtLeastCube realization =
  NatP.≮⇒≥
    (λ tooFew →
      losslessResidualStatesCannotBeFewerThanCube
        tooFew
        realization)

------------------------------------------------------------------------
-- Specialize to the actual live Q1 witness carried by an operational run.
------------------------------------------------------------------------

LosslessResidualOperationalRun :
  (gates : Nat)
  (state : Q2.BoundedSelfReferenceState) →
  Set₁
LosslessResidualOperationalRun gates state =
  Σ
    (Operational.OperationalQ1ConstructionRun state)
    (λ run →
      LosslessResidualStateRealization
        gates
        (Operational.q1WitnessStateCount
          (Operational.q1Witness run)))

------------------------------------------------------------------------
-- Main charged contradiction.
--
-- Operational Q1 already proves:
--
--   stateCount(Q) < recursiveMeasure(state).
--
-- Lossless residual storage proves:
--
--   2^g <= stateCount(Q).
--
-- Hence if recursiveMeasure(state) <= 2^g, no such operational run exists.
------------------------------------------------------------------------

losslessResidualAutomatonCannotCloseWhenCubeReachesMeasure :
  (gates : Nat)
  (state : Q2.BoundedSelfReferenceState) →
  Q2.recursiveMeasure state
    ≤ ResidualBits.bitCardinality gates →
  LosslessResidualOperationalRun gates state →
  ⊥
losslessResidualAutomatonCannotCloseWhenCubeReachesMeasure
    gates
    state
    measureBelowCube
    (run , realization) =
  NatP.<-irrefl
    (Q2.recursiveMeasure state)
    (NatP.≤-<-trans
      measureBelowStateCount
      (Operational.stateCountStrictlyBelowCurrentMeasure run))
  where
    cubeBelowStateCount :
      ResidualBits.bitCardinality gates
      ≤
      Operational.q1WitnessStateCount
        (Operational.q1Witness run)
    cubeBelowStateCount =
      losslessResidualStatesNeedAtLeastCube
        realization

    measureBelowStateCount :
      Q2.recursiveMeasure state
      ≤
      Operational.q1WitnessStateCount
        (Operational.q1Witness run)
    measureBelowStateCount =
      NatP.≤-trans
        measureBelowCube
        cubeBelowStateCount

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The most direct honest builder:
--
--   "state = exact residual vector"
--
-- is now formally eliminated whenever the full residual cube meets/exceeds the
-- self-reference measure.
--
-- A surviving Q1 construction must therefore be genuinely semantic/global:
-- it must identify many distinct raw residual vectors using an independently
-- proved invariant of the SPECIAL self-instantiation family.
--
-- Merely memoizing syntax, local gate errors, or a lossless residual code
-- cannot provide the required compression.
------------------------------------------------------------------------
