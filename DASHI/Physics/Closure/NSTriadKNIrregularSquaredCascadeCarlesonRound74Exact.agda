module DASHI.Physics.Closure.NSTriadKNIrregularSquaredCascadeCarlesonRound74Exact where

------------------------------------------------------------------------
-- ROUND74 / IRREGULAR CASCADE -> SAME CARLESON LEDGER
--
-- The deterministic cascade theorem gives the exact descendant floor mass
--
--   sum_i (r_i mu)^2 = mu^2 sum_i r_i^2.
--
-- This file puts those SAME descendant amplitudes into Round73's finite
-- Carleson ledger.  Each physical child supplies an ACTUAL charge q_i together
-- with only the required inequality
--
--   (r_i mu)^2 <= q_i.
--
-- No charge is manufactured from the floor.  The recursive witness enforces
-- one physical charge per declared child.  If a certified physical Carleson
-- budget funds those nodes, the exact cascade floor mass is therefore <= E.
-- Any physical propagation theorem producing a finite irregular prefix whose
-- squared floor mass exceeds E contradicts the budget immediately.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _*_; _≤_; _<_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNCriticalCauchyCardinalityDilutionNoGoRound71Exact as Mass
import DASHI.Physics.Closure.NSTriadKNPhysicalCarlesonFundingRound73Exact as Carleson
import DASHI.Physics.Closure.NSTriadKNDeterministicIrregularSquaredCascadeRound74Exact as Cascade

data PhysicallyFundedLossChildren
    (parentAmplitude : ℚ) : List ℚ → Set where
  funded[] : PhysicallyFundedLossChildren parentAmplitude []
  funded∷ :
    ∀ {weight rest}
      (actualCharge : ℚ) →
    L2.square (weight * parentAmplitude) ≤ actualCharge →
    PhysicallyFundedLossChildren parentAmplitude rest →
    PhysicallyFundedLossChildren parentAmplitude (weight ∷ rest)

asFundedNodes :
  ∀ {parentAmplitude weights} →
  PhysicallyFundedLossChildren parentAmplitude weights →
  List Carleson.FundedNode
asFundedNodes funded[] = []
asFundedNodes
    (funded∷ {weight = weight} {rest = rest}
      actualCharge floorBelow restWitness) =
  Carleson.funded-node
    (L2.square (weight * _))
    actualCharge
    (L2.squareNonnegative (weight * _))
    floorBelow
  ∷ asFundedNodes restWitness

fundedChildrenFloorMassExact :
  ∀ {parentAmplitude weights}
    (witness : PhysicallyFundedLossChildren parentAmplitude weights) →
  Carleson.sumFloors (asFundedNodes witness)
  ≡ Mass.squaredMass
      (Cascade.irregularChildAmplitudes parentAmplitude weights)
fundedChildrenFloorMassExact funded[] = refl
fundedChildrenFloorMassExact
    (funded∷ {weight = weight} actualCharge floorBelow restWitness) =
  cong
    (L2.square (weight * _) +_)
    (fundedChildrenFloorMassExact restWitness)

irregularCascadeCarlesonBudgetBoundsExactFloorMass :
  ∀ {parentAmplitude weights budget}
    (children : PhysicallyFundedLossChildren parentAmplitude weights) →
  Carleson.PhysicalCarlesonBudget (asFundedNodes children) budget →
  Mass.squaredMass
    (Cascade.irregularChildAmplitudes parentAmplitude weights)
  ≤ budget
irregularCascadeCarlesonBudgetBoundsExactFloorMass children budgetWitness =
  subst
    (_≤ _)
    (fundedChildrenFloorMassExact children)
    (Carleson.carlesonBudgetFundsAllCertifiedFloors budgetWitness)

irregularCascadeFloorAboveBudgetRefutesCarlesonFunding :
  ∀ {parentAmplitude weights budget}
    (children : PhysicallyFundedLossChildren parentAmplitude weights) →
  budget
    < Mass.squaredMass
        (Cascade.irregularChildAmplitudes parentAmplitude weights) →
  ¬ Carleson.PhysicalCarlesonBudget (asFundedNodes children) budget
irregularCascadeFloorAboveBudgetRefutesCarlesonFunding children excess =
  Carleson.floorPrefixAboveBudgetRefutesCarlesonFunding
    (subst
      (_ <_)
      (sym (fundedChildrenFloorMassExact children))
      excess)

round74IrregularSquaredCascadeWeldedToCarlesonLedger : Bool
round74IrregularSquaredCascadeWeldedToCarlesonLedger = true

round74PhysicalIrregularDescendantChargeWitnessConstructed : Bool
round74PhysicalIrregularDescendantChargeWitnessConstructed = false

round74IrregularSquaredCascadeWeldedToCarlesonLedgerIsTrue :
  round74IrregularSquaredCascadeWeldedToCarlesonLedger ≡ true
round74IrregularSquaredCascadeWeldedToCarlesonLedgerIsTrue = refl
