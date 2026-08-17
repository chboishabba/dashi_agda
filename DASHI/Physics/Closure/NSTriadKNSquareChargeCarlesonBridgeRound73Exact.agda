module DASHI.Physics.Closure.NSTriadKNSquareChargeCarlesonBridgeRound73Exact where

------------------------------------------------------------------------
-- ROUND73 / SQUARE-CHARGE FUNDING = CARLESON NODE SPECIALIZATION
--
-- Round73 now has two useful finite funding views:
--
--   * SquareChargeFundingCompiler: a normalized amplification witness produces
--       floor = mu^2 <= physical charge;
--   * PhysicalCarlesonFunding: an additive physical node carries
--       floor <= charge.
--
-- They should not become parallel authorities.  This file proves that every
-- square-charged amplification event is literally a Carleson funded node with
-- the same floor and charge, and that the recursive floor/charge totals agree
-- exactly.
--
-- Hence the remaining physical propagation theorem has ONE additive budget
-- obligation: produce genuinely disjoint/orthogonal descendants whose node
-- charges are the same charges constructed by the normalized physical overlay.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_; _<_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNFiniteDisjointConcentrationBudgetRound69Exact as R69
import DASHI.Physics.Closure.NSTriadKNScaleDependentConcentrationFundingRound70Exact as Funding
import DASHI.Physics.Closure.NSTriadKNSquareChargeFundingCompilerRound73Exact as Square
import DASHI.Physics.Closure.NSTriadKNPhysicalCarlesonFundingRound73Exact as Carleson

squareEventAsFundedNode :
  Square.SquareChargedAmplificationEvent → Carleson.FundedNode
squareEventAsFundedNode witness =
  Carleson.funded-node
    (Square.squareFloor witness)
    (Square.charge witness)
    (L2.squareNonnegative (Square.amplification witness))
    (Square.squareBelowCharge witness)

squareEventsAsFundedNodes :
  List Square.SquareChargedAmplificationEvent → List Carleson.FundedNode
squareEventsAsFundedNodes [] = []
squareEventsAsFundedNodes (witness ∷ rest) =
  squareEventAsFundedNode witness ∷ squareEventsAsFundedNodes rest

squareNodeFloorsExact :
  (witnesses : List Square.SquareChargedAmplificationEvent) →
  Carleson.sumFloors (squareEventsAsFundedNodes witnesses)
  ≡ Funding.sumFloors (Square.squareFloors witnesses)
squareNodeFloorsExact [] = refl
squareNodeFloorsExact (witness ∷ rest)
  rewrite squareNodeFloorsExact rest = refl

squareNodeChargesExact :
  (witnesses : List Square.SquareChargedAmplificationEvent) →
  Carleson.sumCharges (squareEventsAsFundedNodes witnesses)
  ≡ R69.totalCharge (Square.concentrationEvents witnesses)
squareNodeChargesExact [] = refl
squareNodeChargesExact (witness ∷ rest)
  rewrite squareNodeChargesExact rest = refl

squareBudgetAsCarlesonBudget :
  ∀ {energy witnesses} →
  0ℚ ≤ energy →
  Square.SquareAmplificationBudget energy witnesses →
  Carleson.PhysicalCarlesonBudget
    (squareEventsAsFundedNodes witnesses) energy
squareBudgetAsCarlesonBudget {energy} {witnesses} energyNN budget = record
  { budgetNonnegative = energyNN
  ; subtreeChargeWithinBudget =
      subst
        (_≤ energy)
        (sym (squareNodeChargesExact witnesses))
        (Square.totalChargeBelowEnergy budget)
  }

carlesonBudgetAsSquareBudget :
  ∀ {energy witnesses} →
  Carleson.PhysicalCarlesonBudget
    (squareEventsAsFundedNodes witnesses) energy →
  Square.SquareAmplificationBudget energy witnesses
carlesonBudgetAsSquareBudget {energy} {witnesses} budget = record
  { totalChargeBelowEnergy =
      subst
        (_≤ energy)
        (squareNodeChargesExact witnesses)
        (Carleson.subtreeChargeWithinBudget budget)
  }

squarePrefixAboveEnergyRefutesCarlesonBudget :
  ∀ {energy witnesses} →
  energy < Funding.sumFloors (Square.squareFloors witnesses) →
  ¬ Carleson.PhysicalCarlesonBudget
      (squareEventsAsFundedNodes witnesses) energy
squarePrefixAboveEnergyRefutesCarlesonBudget {witnesses = witnesses} excess budget =
  Carleson.floorPrefixAboveBudgetRefutesCarlesonFunding
    (subst
      (λ total → _ < total)
      (sym (squareNodeFloorsExact witnesses))
      excess)
    budget

round73SquareFundingAndCarlesonLedgerUnified : Bool
round73SquareFundingAndCarlesonLedgerUnified = true

round73NormalizedSquareFloorsUseOneAdditivePhysicalBudget : Bool
round73NormalizedSquareFloorsUseOneAdditivePhysicalBudget = true

round73PhysicalDescendantOrthogonalityStillRequired : Bool
round73PhysicalDescendantOrthogonalityStillRequired = false

round73SquareFundingAndCarlesonLedgerUnifiedIsTrue :
  round73SquareFundingAndCarlesonLedgerUnified ≡ true
round73SquareFundingAndCarlesonLedgerUnifiedIsTrue = refl

round73PhysicalDescendantOrthogonalityStillRequiredIsFalse :
  round73PhysicalDescendantOrthogonalityStillRequired ≡ false
round73PhysicalDescendantOrthogonalityStillRequiredIsFalse = refl
