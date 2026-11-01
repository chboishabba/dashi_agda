module DASHI.Physics.Closure.NSTriadKNFiniteDisjointConcentrationBudgetRound69Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tobias Barker; Christophe Prange.
-- Title: "Quantitative Regularity for the Navier-Stokes Equations Via
-- Spatial Concentration".
-- DOI: 10.1007/s00220-021-04122-x.
--
-- Author: Terence Tao.
-- Title: "Quantitative bounds for critically bounded solutions to the
-- Navier-Stokes equations".
-- DOI: 10.1090/PSPUM/104/01874.
--
-- Authors: Luis Caffarelli; Robert Kohn; Louis Nirenberg.
-- Title: "Partial regularity of suitable weak solutions of the
-- Navier-Stokes equations".
-- DOI: 10.1002/cpa.3160350604.
--
-- ROUND 69 / FINITE CONCENTRATION FUNDING
--
-- The spatial-concentration strategy ultimately needs a counting/funding step:
-- sufficiently separated concentration events cannot each consume a fixed
-- positive amount of one globally finite budget indefinitely.
--
-- This file proves the finite arithmetic core without assuming any Navier-
-- Stokes regularity statement.  A list of concentration events carries literal
-- nonnegative charges.  If every event carries at least mu, then the recursively
-- accumulated minimum funding cost is bounded by the actual total charge.  If
-- that total charge is in turn bounded by an energy/enstrophy budget E, then
-- the minimum funding cost is <= E.
--
-- No claim is made here that the current DASHI localized shell remainder is
-- such a disjoint physical charge.  That same-object identification is the
-- next PDE theorem and is intentionally kept fail-closed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

record ConcentrationEvent : Set where
  constructor concentration-event
  field
    charge : ℚ
    chargeNonnegative : 0ℚ ≤ charge

open ConcentrationEvent public

totalCharge : List ConcentrationEvent → ℚ
totalCharge [] = 0ℚ
totalCharge (event ∷ rest) = charge event + totalCharge rest

minimumFunding : ℚ → List ConcentrationEvent → ℚ
minimumFunding mu [] = 0ℚ
minimumFunding mu (event ∷ rest) = mu + minimumFunding mu rest

data EveryEventCarriesAtLeast (mu : ℚ) : List ConcentrationEvent → Set where
  floor[] : EveryEventCarriesAtLeast mu []
  floor∷ : ∀ {event rest} →
    mu ≤ charge event →
    EveryEventCarriesAtLeast mu rest →
    EveryEventCarriesAtLeast mu (event ∷ rest)

minimumFundingBelowTotalCharge :
  ∀ {mu events} →
  EveryEventCarriesAtLeast mu events →
  minimumFunding mu events ≤ totalCharge events
minimumFundingBelowTotalCharge floor[] = ℚP.≤-refl
minimumFundingBelowTotalCharge (floor∷ headFloor tailFloor) =
  ℚP.+-mono-≤ headFloor (minimumFundingBelowTotalCharge tailFloor)

record FiniteConcentrationBudget
    (mu energy : ℚ)
    (events : List ConcentrationEvent) : Set where
  field
    eventFloor : EveryEventCarriesAtLeast mu events
    totalChargeBelowEnergy : totalCharge events ≤ energy

open FiniteConcentrationBudget public

minimumFundingBelowEnergy :
  ∀ {mu energy events} →
  FiniteConcentrationBudget mu energy events →
  minimumFunding mu events ≤ energy
minimumFundingBelowEnergy budget =
  ℚP.≤-trans
    (minimumFundingBelowTotalCharge (eventFloor budget))
    (totalChargeBelowEnergy budget)

-- Splitting a sequence of events into two disjoint ledgers is additive at the
-- funding level.  This is the exact finite analogue of summing separated
-- annuli/epochs only after their charges have been assigned once.
append : ∀ {A : Set} → List A → List A → List A
append [] right = right
append (x ∷ xs) right = x ∷ append xs right

minimumFundingAppend : ∀ mu left right →
  minimumFunding mu (append left right)
  ≡ minimumFunding mu left + minimumFunding mu right
minimumFundingAppend mu [] right =
  sym (ℚP.+-identityˡ (minimumFunding mu right))
minimumFundingAppend mu (event ∷ rest) right =
  trans
    (cong (mu +_) (minimumFundingAppend mu rest right))
    (sym (ℚP.+-assoc mu (minimumFunding mu rest) (minimumFunding mu right)))

totalChargeAppend : ∀ left right →
  totalCharge (append left right)
  ≡ totalCharge left + totalCharge right
totalChargeAppend [] right =
  sym (ℚP.+-identityˡ (totalCharge right))
totalChargeAppend (event ∷ rest) right =
  trans
    (cong (charge event +_) (totalChargeAppend rest right))
    (sym (ℚP.+-assoc (charge event) (totalCharge rest) (totalCharge right)))

round69FiniteConcentrationFundingConstructed : Bool
round69FiniteConcentrationFundingConstructed = true

round69PhysicalDisjointChargeIdentificationConstructed : Bool
round69PhysicalDisjointChargeIdentificationConstructed = false

round69FiniteConcentrationFundingConstructedIsTrue :
  round69FiniteConcentrationFundingConstructed ≡ true
round69FiniteConcentrationFundingConstructedIsTrue = refl

round69PhysicalDisjointChargeIdentificationConstructedIsFalse :
  round69PhysicalDisjointChargeIdentificationConstructed ≡ false
round69PhysicalDisjointChargeIdentificationConstructedIsFalse = refl
