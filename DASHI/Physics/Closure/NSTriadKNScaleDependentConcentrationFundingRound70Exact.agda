module DASHI.Physics.Closure.NSTriadKNScaleDependentConcentrationFundingRound70Exact where

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
-- ROUND 70 / SCALE-DEPENDENT FUNDING CRITERION
--
-- Round69 used one fixed event floor mu and therefore obtained the familiar
-- funding inequality N*mu <= E.  For a propagation theorem whose constants
-- degrade with scale this is unnecessarily restrictive.  The exact necessary
-- arithmetic object is the SUM of the individual event floors.
--
-- For events e_i with lower bounds floor_i <= charge_i,
--
--       sum_i floor_i <= sum_i charge_i <= E.
--
-- Hence a proposed propagation mechanism yields a contradiction exactly when
-- it can produce a finite prefix whose cumulative floor exceeds E.  Uniform
-- mu>0 is one sufficient route; it is not required.
--
-- Conversely, if the proposed floors themselves have cumulative sum <= E,
-- there is an explicit compatible event ledger with charge_i=floor_i.  Thus
-- the finite-funding argument ALONE cannot turn a summable/degrading sequence
-- of lower bounds into an invariant critical barrier.
--
-- This is the quantitative falsification boundary for Round70: Carleman or
-- other propagation constants may vary with scale, but their resulting charge
-- floors must have unbounded-enough cumulative mass to outrun the one finite
-- physical budget.  Exponential degradation is therefore dangerous precisely
-- when it makes those floors summable.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.Physics.Closure.NSTriadKNFiniteDisjointConcentrationBudgetRound69Exact as R69

sumFloors : List ℚ → ℚ
sumFloors [] = 0ℚ
sumFloors (floor ∷ rest) = floor + sumFloors rest

data EventwiseFloors : List ℚ → List R69.ConcentrationEvent → Set where
  floors[] : EventwiseFloors [] []
  floors∷ : ∀ {floor floors event events} →
    floor ≤ R69.charge event →
    EventwiseFloors floors events →
    EventwiseFloors (floor ∷ floors) (event ∷ events)

scaleDependentFundingBelowTotalCharge :
  ∀ {floors events} →
  EventwiseFloors floors events →
  sumFloors floors ≤ R69.totalCharge events
scaleDependentFundingBelowTotalCharge floors[] = ℚP.≤-refl
scaleDependentFundingBelowTotalCharge (floors∷ headFloor tailFloors) =
  ℚP.+-mono-≤ headFloor (scaleDependentFundingBelowTotalCharge tailFloors)

record ScaleDependentConcentrationBudget
    (energy : ℚ)
    (floors : List ℚ)
    (events : List R69.ConcentrationEvent) : Set where
  field
    eventwiseFloors : EventwiseFloors floors events
    totalChargeBelowEnergy : R69.totalCharge events ≤ energy

open ScaleDependentConcentrationBudget public

scaleDependentFundingBelowEnergy :
  ∀ {energy floors events} →
  ScaleDependentConcentrationBudget energy floors events →
  sumFloors floors ≤ energy
scaleDependentFundingBelowEnergy budget =
  ℚP.≤-trans
    (scaleDependentFundingBelowTotalCharge (eventwiseFloors budget))
    (totalChargeBelowEnergy budget)

-- Any finite propagated prefix whose required cumulative floor is already
-- larger than the available energy cannot be physically funded.
prefixFloorAboveEnergyContradictsBudget :
  ∀ {energy floors events} →
  energy < sumFloors floors →
  ¬ ScaleDependentConcentrationBudget energy floors events
prefixFloorAboveEnergyContradictsBudget excess budget =
  ℚP.<-irrefl energy
    (ℚP.<-≤-trans excess (scaleDependentFundingBelowEnergy budget))

------------------------------------------------------------------------
-- Exact no-go for summable/degraded floors at the funding layer.
--
-- If all floors are nonnegative, choose event charge exactly equal to its
-- floor.  The resulting total charge is exactly the cumulative floor.  Thus
-- whenever sumFloors floors <= E there EXISTS a perfectly valid event ledger
-- funded by E.  Additional PDE structure would be needed for a contradiction.
------------------------------------------------------------------------

data AllFloorsNonnegative : List ℚ → Set where
  nonnegative[] : AllFloorsNonnegative []
  nonnegative∷ : ∀ {floor rest} →
    0ℚ ≤ floor →
    AllFloorsNonnegative rest →
    AllFloorsNonnegative (floor ∷ rest)

exactFloorEvents :
  (floors : List ℚ) →
  AllFloorsNonnegative floors →
  List R69.ConcentrationEvent
exactFloorEvents [] nonnegative[] = []
exactFloorEvents (floor ∷ rest) (nonnegative∷ floorNN restNN) =
  R69.concentration-event floor floorNN ∷ exactFloorEvents rest restNN

exactFloorEventsTotal :
  (floors : List ℚ) →
  (nonnegative : AllFloorsNonnegative floors) →
  R69.totalCharge (exactFloorEvents floors nonnegative) ≡ sumFloors floors
exactFloorEventsTotal [] nonnegative[] = refl
exactFloorEventsTotal (floor ∷ rest) (nonnegative∷ floorNN restNN) =
  cong (floor +_) (exactFloorEventsTotal rest restNN)

exactFloorEventsMeetFloors :
  (floors : List ℚ) →
  (nonnegative : AllFloorsNonnegative floors) →
  EventwiseFloors floors (exactFloorEvents floors nonnegative)
exactFloorEventsMeetFloors [] nonnegative[] = floors[]
exactFloorEventsMeetFloors (floor ∷ rest) (nonnegative∷ floorNN restNN) =
  floors∷ ℚP.≤-refl (exactFloorEventsMeetFloors rest restNN)

summableFloorsAdmitFundedLedger :
  ∀ {energy floors} →
  (nonnegative : AllFloorsNonnegative floors) →
  sumFloors floors ≤ energy →
  ScaleDependentConcentrationBudget
    energy floors (exactFloorEvents floors nonnegative)
summableFloorsAdmitFundedLedger {energy} {floors} nonnegative funded = record
  { eventwiseFloors = exactFloorEventsMeetFloors floors nonnegative
  ; totalChargeBelowEnergy =
      let exact = exactFloorEventsTotal floors nonnegative
      in Relation.Binary.PropositionalEquality.subst
           (_≤ energy) (sym exact) funded
  }

round70ScaleDependentFundingCriterionConstructed : Bool
round70ScaleDependentFundingCriterionConstructed = true

round70UniformPerEventFloorRequired : Bool
round70UniformPerEventFloorRequired = false

round70SummableFloorFundingNoGoConstructed : Bool
round70SummableFloorFundingNoGoConstructed = true

round70PhysicalPropagationProducesDivergentCumulativeFloor : Bool
round70PhysicalPropagationProducesDivergentCumulativeFloor = false

round70ScaleDependentFundingCriterionConstructedIsTrue :
  round70ScaleDependentFundingCriterionConstructed ≡ true
round70ScaleDependentFundingCriterionConstructedIsTrue = refl

round70UniformPerEventFloorRequiredIsFalse :
  round70UniformPerEventFloorRequired ≡ false
round70UniformPerEventFloorRequiredIsFalse = refl

round70SummableFloorFundingNoGoConstructedIsTrue :
  round70SummableFloorFundingNoGoConstructed ≡ true
round70SummableFloorFundingNoGoConstructedIsTrue = refl

round70PhysicalPropagationProducesDivergentCumulativeFloorIsFalse :
  round70PhysicalPropagationProducesDivergentCumulativeFloor ≡ false
round70PhysicalPropagationProducesDivergentCumulativeFloorIsFalse = refl
