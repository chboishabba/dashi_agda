module DASHI.Physics.Closure.NSTriadKNFrameWeightedFinalAntichainBudgetRound77Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Lennart Carleson.
-- Classical Carleson-measure framework; the exact finite ledger used here is
-- repository-local ordered finite algebra.
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- DOI: 10.1063/1.858309.
-- Candidate-sector guidance only; no statistical transfer conclusion is used.
--
-- ROUND77 / FRAME-WEIGHTED ROUTE-B COMPILER
--
-- Round77 replaces the artificial unit frame normalization by an exact
-- reciprocal weight rho.  The admissible floor at an event is therefore
--
--   rho mu^2 <= physicalCharge.
--
-- The one-step propagation compiler proves
--
--   M_(j+1) = M_j + mu_j^2 epsilon_j
--
-- under the frame-weighted threshold
--
--   sum_i rho_i r_i^2 = rho_parent + epsilon_j.
--
-- This file telescopes those weighted steps and feeds only ONE final antichain
-- to the already-existing physical Carleson ledger.  It therefore preserves
-- Round76's key economy: no cross-generation charge additivity is needed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNFrameWeightedSupercriticalPropagationRound77Exact as Weighted
import DASHI.Physics.Closure.NSTriadKNPhysicalCarlesonFundingRound73Exact as Carleson

record WeightedAntichainStep : Set where
  constructor weighted-antichain-step
  field
    parentMass childMass excessMass : ℚ
    exactGrowth : childMass ≡ parentMass + excessMass

open WeightedAntichainStep public

fromWeightedRow : Weighted.FrameWeightedSupercriticalRow → WeightedAntichainStep
fromWeightedRow row =
  weighted-antichain-step
    (Weighted.weightedParentMass
      (Weighted.parentWeight row)
      (Weighted.parentAmplitude row))
    (Weighted.sumGuaranteedChildFloors (Weighted.children row))
    (L2.square (Weighted.parentAmplitude row) * Weighted.excess row)
    (Weighted.weightedSupercriticalGuaranteedGrowthExact row)

data WeightedAntichainHistory : ℚ → ℚ → Set where
  seed : (mass : ℚ) → WeightedAntichainHistory mass mass
  extend :
    ∀ {initial current}
      (history : WeightedAntichainHistory initial current)
      (step : WeightedAntichainStep) →
    parentMass step ≡ current →
    WeightedAntichainHistory initial (childMass step)

cumulativeWeightedFrameExcess :
  ∀ {initial final} → WeightedAntichainHistory initial final → ℚ
cumulativeWeightedFrameExcess (seed mass) = 0ℚ
cumulativeWeightedFrameExcess (extend history step alignment) =
  cumulativeWeightedFrameExcess history + excessMass step

weightedHistoryFinalMassExact :
  ∀ {initial final}
    (history : WeightedAntichainHistory initial final) →
  final ≡ initial + cumulativeWeightedFrameExcess history
weightedHistoryFinalMassExact (seed mass) = solve (mass ∷ [])
weightedHistoryFinalMassExact
    {initial} (extend {current = current} history step alignment) =
  trans
    (exactGrowth step)
    (trans
      (cong (_+ excessMass step) alignment)
      (trans
        (cong (_+ excessMass step) (weightedHistoryFinalMassExact history))
        (solve
          ( initial
          ∷ cumulativeWeightedFrameExcess history
          ∷ excessMass step
          ∷ []))))

weightedCumulativeExcessAboveBudgetForcesFinalAbove :
  ∀ {initial final budget}
    (history : WeightedAntichainHistory initial final) →
  budget < initial + cumulativeWeightedFrameExcess history →
  budget < final
weightedCumulativeExcessAboveBudgetForcesFinalAbove
    {budget = budget} history above =
  subst (budget <_) (sym (weightedHistoryFinalMassExact history)) above

record FrameWeightedFundedNode : Set where
  constructor frame-weighted-funded-node
  field
    weight amplitude charge : ℚ
    weightNonnegative : 0ℚ ≤ weight
    floorBelowCharge : weight * L2.square amplitude ≤ charge

open FrameWeightedFundedNode public

asCarlesonNode : FrameWeightedFundedNode → Carleson.FundedNode
asCarlesonNode node =
  Carleson.funded-node
    (weight node * L2.square (amplitude node))
    (charge node)
    (ℚP.0≤*0≤ (weightNonnegative node) (L2.squareNonnegative (amplitude node)))
    (floorBelowCharge node)

asCarlesonNodes : List FrameWeightedFundedNode → List Carleson.FundedNode
asCarlesonNodes [] = []
asCarlesonNodes (node ∷ rest) = asCarlesonNode node ∷ asCarlesonNodes rest

weightedFloorMass : List FrameWeightedFundedNode → ℚ
weightedFloorMass [] = 0ℚ
weightedFloorMass (node ∷ rest) =
  weight node * L2.square (amplitude node) + weightedFloorMass rest

weightedFloorMassExact :
  ∀ nodes →
  Carleson.sumFloors (asCarlesonNodes nodes) ≡ weightedFloorMass nodes
weightedFloorMassExact [] = refl
weightedFloorMassExact (node ∷ rest) =
  cong
    (weight node * L2.square (amplitude node) +_)
    (weightedFloorMassExact rest)

weightedFinalAntichainAboveBudgetRefutesFunding :
  ∀ {nodes budget} →
  budget < weightedFloorMass nodes →
  ¬ Carleson.PhysicalCarlesonBudget (asCarlesonNodes nodes) budget
weightedFinalAntichainAboveBudgetRefutesFunding {nodes} {budget} above =
  Carleson.floorPrefixAboveBudgetRefutesCarlesonFunding
    (subst (budget <_) (sym (weightedFloorMassExact nodes)) above)

record FinalWeightedAntichainRealization (finalMass : ℚ) : Set where
  field
    nodes : List FrameWeightedFundedNode
    floorMassExact : weightedFloorMass nodes ≡ finalMass

open FinalWeightedAntichainRealization public

frameWeightedRouteBContradiction :
  ∀ {initial final budget}
    (history : WeightedAntichainHistory initial final)
    (realization : FinalWeightedAntichainRealization final) →
  budget < initial + cumulativeWeightedFrameExcess history →
  ¬ Carleson.PhysicalCarlesonBudget
      (asCarlesonNodes (nodes realization)) budget
frameWeightedRouteBContradiction {budget = budget}
    history realization cumulativeAbove =
  let
    finalAbove = weightedCumulativeExcessAboveBudgetForcesFinalAbove
      history cumulativeAbove
    floorAbove = subst (budget <_)
      (sym (floorMassExact realization))
      finalAbove
  in
  weightedFinalAntichainAboveBudgetRefutesFunding floorAbove

round77FrameWeightedHistoryTelescopesExactly : Bool
round77FrameWeightedHistoryTelescopesExactly = true

round77FrameWeightedFinalAntichainContradictionConstructed : Bool
round77FrameWeightedFinalAntichainContradictionConstructed = true

round77CrossGenerationChargeAdditivityRequired : Bool
round77CrossGenerationChargeAdditivityRequired = false

round77PhysicalFinalAntichainRealizationConstructed : Bool
round77PhysicalFinalAntichainRealizationConstructed = false

round77PositiveCumulativePhysicalWeightedExcessConstructed : Bool
round77PositiveCumulativePhysicalWeightedExcessConstructed = false

round77FrameWeightedFinalAntichainContradictionConstructedIsTrue :
  round77FrameWeightedFinalAntichainContradictionConstructed ≡ true
round77FrameWeightedFinalAntichainContradictionConstructedIsTrue = refl

round77CrossGenerationChargeAdditivityRequiredIsFalse :
  round77CrossGenerationChargeAdditivityRequired ≡ false
round77CrossGenerationChargeAdditivityRequiredIsFalse = refl
