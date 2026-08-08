module DASHI.Physics.Closure.NSTriadKNHHBadFeasibilityRound29Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for the
-- Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- DASHI CONTRIBUTION
--
-- Make the good/bad high-high route falsifiable before further investment. A
-- feasible parameter choice must put the sum of variation, amplitude and
-- crossing costs strictly below the owner's allocation. If an unavoidable
-- lower floor is already at least the allocation, the current estimate family
-- is proved impossible.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Data.Rational.Base using (ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)

record BudgetOrder : Set₁ where
  field
    _≤ᵇ_ _<ᵇ_ : ℚ → ℚ → Set
    ≤-<-trans : ∀ {a b c} → a ≤ᵇ b → b <ᵇ c → a <ᵇ c
    <-≤-trans : ∀ {a b c} → a <ᵇ b → b ≤ᵇ c → a <ᵇ c
    <-irrefl : ∀ value → ¬ (value <ᵇ value)

open BudgetOrder public

record HHBadCostData : Set where
  constructor hh-bad-cost-data
  field
    variationCost amplitudeCost crossingCost : ℚ

open HHBadCostData public

totalHHBadCost : HHBadCostData → ℚ
totalHHBadCost costs =
  variationCost costs + amplitudeCost costs + crossingCost costs

record HHBadFeasible
    (order : BudgetOrder)
    (costs : HHBadCostData) : Set where
  constructor hh-bad-feasible
  field
    allocatedViscosity : ℚ
    strictClosure :
      _<ᵇ_ order (totalHHBadCost costs) allocatedViscosity

open HHBadFeasible public

record HHBadUnavoidableFloor
    (order : BudgetOrder)
    (costs : HHBadCostData)
    (feasible : HHBadFeasible order costs) : Set where
  constructor hh-bad-unavoidable-floor
  field
    floor : ℚ
    floorBelowCurrentCost :
      _≤ᵇ_ order floor (totalHHBadCost costs)
    allocationBelowFloor :
      _≤ᵇ_ order (allocatedViscosity feasible) floor

open HHBadUnavoidableFloor public

unavoidableFloorRefutesCurrentHHBadFamily :
  (order : BudgetOrder) →
  (costs : HHBadCostData) →
  (feasible : HHBadFeasible order costs) →
  HHBadUnavoidableFloor order costs feasible → ⊥
unavoidableFloorRefutesCurrentHHBadFamily order costs feasible obstruction =
  <-irrefl order (floor obstruction)
    (<-≤-trans order
      (≤-<-trans order
        (floorBelowCurrentCost obstruction)
        (strictClosure feasible))
      (allocationBelowFloor obstruction))

record HysteresisThresholdData : Set where
  constructor hysteresis-threshold-data
  field
    goodThreshold badThreshold : ℚ

open HysteresisThresholdData public

record HHBadParameterCandidate
    (order : BudgetOrder) : Set where
  constructor hh-bad-parameter-candidate
  field
    thresholds : HysteresisThresholdData
    thresholdSeparated :
      _<ᵇ_ order
        (goodThreshold thresholds)
        (badThreshold thresholds)
    costs : HHBadCostData
    allocation : ℚ
    costFitsAllocation :
      _<ᵇ_ order (totalHHBadCost costs) allocation

open HHBadParameterCandidate public

candidateProducesFeasibleBudget :
  (order : BudgetOrder) →
  (candidate : HHBadParameterCandidate order) →
  HHBadFeasible order (costs candidate)
candidateProducesFeasibleBudget order candidate =
  hh-bad-feasible
    (allocation candidate)
    (costFitsAllocation candidate)

costRegrouping :
  (variation amplitude crossing : ℚ) →
  totalHHBadCost
    (hh-bad-cost-data variation amplitude crossing)
  ≡ variation + (amplitude + crossing)
costRegrouping variation amplitude crossing =
  solve (variation ∷ amplitude ∷ crossing ∷ [])

hhBadFeasibilityCriterionClosed : Bool
hhBadFeasibilityCriterionClosed = true

physicalHHBadParameterTupleConstructed : Bool
physicalHHBadParameterTupleConstructed = false

hhBadFeasibilityCriterionClosedIsTrue :
  hhBadFeasibilityCriterionClosed ≡ true
hhBadFeasibilityCriterionClosedIsTrue = refl

physicalHHBadParameterTupleConstructedIsFalse :
  physicalHHBadParameterTupleConstructed ≡ false
physicalHHBadParameterTupleConstructedIsFalse = refl
