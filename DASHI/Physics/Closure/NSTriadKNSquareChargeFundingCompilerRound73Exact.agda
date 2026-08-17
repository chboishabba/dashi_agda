module DASHI.Physics.Closure.NSTriadKNSquareChargeFundingCompilerRound73Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Terence Tao.
-- Title: "Quantitative bounds for critically bounded solutions to the
-- Navier-Stokes equations".
-- DOI: 10.1090/PSPUM/104/01874.
--
-- Authors: Tobias Barker; Christophe Prange.
-- Title: "Quantitative Regularity for the Navier-Stokes Equations Via
-- Spatial Concentration".
-- DOI: 10.1007/s00220-021-04122-x.
--
-- ROUND73 / SQUARE-CHARGE FUNDING COMPILER
--
-- The normalized effective-complexity theorem gives the physical shape
--
--      mu^2 <= charge(event).
--
-- This file compiles a finite list of such witnesses into the exact Round70
-- scale-dependent funding language.  The floor list is not supplied
-- independently: it is definitionally the list of amplification squares, and
-- the event list is definitionally the list of the same witnessed charges.
--
-- Therefore
--
--      sum_i mu_i^2 <= totalCharge(events) <= E.
--
-- Any finite prefix whose squared-amplification total exceeds E is impossible.
-- This is the precise denominator-free bridge from Round73 normalized
-- concentration to the Round70 finite-budget contradiction.
--
-- No claim is made here that the events are physically separated.  The
-- remaining PDE theorem must produce duplicate-free physical events carrying
-- these witnessed charges from the selected localized trajectory.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNFiniteDisjointConcentrationBudgetRound69Exact as R69
import DASHI.Physics.Closure.NSTriadKNScaleDependentConcentrationFundingRound70Exact as Funding

record SquareChargedAmplificationEvent : Set where
  constructor square-charged-amplification-event
  field
    amplification : ℚ
    charge : ℚ
    chargeNonnegative : 0ℚ ≤ charge
    squareBelowCharge : L2.square amplification ≤ charge

open SquareChargedAmplificationEvent public

asConcentrationEvent : SquareChargedAmplificationEvent → R69.ConcentrationEvent
asConcentrationEvent witness =
  R69.concentration-event (charge witness) (chargeNonnegative witness)

squareFloor : SquareChargedAmplificationEvent → ℚ
squareFloor witness = L2.square (amplification witness)

squareFloors : List SquareChargedAmplificationEvent → List ℚ
squareFloors [] = []
squareFloors (witness ∷ rest) = squareFloor witness ∷ squareFloors rest

concentrationEvents :
  List SquareChargedAmplificationEvent → List R69.ConcentrationEvent
concentrationEvents [] = []
concentrationEvents (witness ∷ rest) =
  asConcentrationEvent witness ∷ concentrationEvents rest

squareFloorsNonnegative :
  (witnesses : List SquareChargedAmplificationEvent) →
  Funding.AllFloorsNonnegative (squareFloors witnesses)
squareFloorsNonnegative [] = Funding.nonnegative[]
squareFloorsNonnegative (witness ∷ rest) =
  Funding.nonnegative∷
    (L2.squareNonnegative (amplification witness))
    (squareFloorsNonnegative rest)

squareFloorsMeetWitnessedCharges :
  (witnesses : List SquareChargedAmplificationEvent) →
  Funding.EventwiseFloors
    (squareFloors witnesses)
    (concentrationEvents witnesses)
squareFloorsMeetWitnessedCharges [] = Funding.floors[]
squareFloorsMeetWitnessedCharges (witness ∷ rest) =
  Funding.floors∷
    (squareBelowCharge witness)
    (squareFloorsMeetWitnessedCharges rest)

squareFundingBelowTotalCharge :
  (witnesses : List SquareChargedAmplificationEvent) →
  Funding.sumFloors (squareFloors witnesses)
  ≤ R69.totalCharge (concentrationEvents witnesses)
squareFundingBelowTotalCharge witnesses =
  Funding.scaleDependentFundingBelowTotalCharge
    (squareFloorsMeetWitnessedCharges witnesses)

record SquareAmplificationBudget
    (energy : ℚ)
    (witnesses : List SquareChargedAmplificationEvent) : Set where
  field
    totalChargeBelowEnergy :
      R69.totalCharge (concentrationEvents witnesses) ≤ energy

open SquareAmplificationBudget public

squareFundingBelowEnergy :
  ∀ {energy witnesses} →
  SquareAmplificationBudget energy witnesses →
  Funding.sumFloors (squareFloors witnesses) ≤ energy
squareFundingBelowEnergy {witnesses = witnesses} budget =
  ℚP.≤-trans
    (squareFundingBelowTotalCharge witnesses)
    (totalChargeBelowEnergy budget)

squareAmplificationPrefixAboveEnergyImpossible :
  ∀ {energy witnesses} →
  energy < Funding.sumFloors (squareFloors witnesses) →
  ¬ SquareAmplificationBudget energy witnesses
squareAmplificationPrefixAboveEnergyImpossible excess budget =
  ℚP.<-irrefl _
    (ℚP.<-≤-trans excess (squareFundingBelowEnergy budget))

asRound70Budget :
  ∀ {energy witnesses} →
  SquareAmplificationBudget energy witnesses →
  Funding.ScaleDependentConcentrationBudget
    energy
    (squareFloors witnesses)
    (concentrationEvents witnesses)
asRound70Budget budget = record
  { Funding.eventwiseFloors = squareFloorsMeetWitnessedCharges _
  ; Funding.totalChargeBelowEnergy = totalChargeBelowEnergy budget
  }

round73SquareAmplificationFundingCompilerConstructed : Bool
round73SquareAmplificationFundingCompilerConstructed = true

round73SquaredFloorsAreDerivedFromSameWitnessedEvents : Bool
round73SquaredFloorsAreDerivedFromSameWitnessedEvents = true

round73PhysicalDuplicateFreeSquareChargedEventsConstructed : Bool
round73PhysicalDuplicateFreeSquareChargedEventsConstructed = false

round73SquareAmplificationFundingCompilerConstructedIsTrue :
  round73SquareAmplificationFundingCompilerConstructed ≡ true
round73SquareAmplificationFundingCompilerConstructedIsTrue = refl

round73PhysicalDuplicateFreeSquareChargedEventsConstructedIsFalse :
  round73PhysicalDuplicateFreeSquareChargedEventsConstructed ≡ false
round73PhysicalDuplicateFreeSquareChargedEventsConstructedIsFalse = refl
