module DASHI.Physics.Closure.NSTriadKNLuoStrictLossCrossPollinationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Michel Bony,
-- "Calcul symbolique et propagation des singularites pour les equations aux
-- derivees partielles non lineaires", Annales scientifiques de l'Ecole
-- Normale Superieure 14 (1981), 209--246.
-- DOI: 10.24033/asens.1404.
--
-- Peter Constantin and Ciprian Foias,
-- "Navier--Stokes Equations", University of Chicago Press, 1988.
-- DOI: 10.7208/chicago/9780226115498.001.0001.
--
-- James Serrin,
-- "On the Interior Regularity of Weak Solutions of the Navier--Stokes
-- Equations", Archive for Rational Mechanics and Analysis 9 (1962), 187--195.
-- DOI: 10.1007/BF00253344.
--
-- DASHI CONTRIBUTION
--
-- Instantiate the shared weighted strict-loss algebra for the four Bony
-- interaction classes.  With unit transfer factors the inherited floor is
-- exactly terminal dissipation minus LH, HL, CC and HH losses.  Strict slack
-- yields a positive surviving margin; mere nonnegative admissibility yields
-- only a zero margin.
--
-- The classwise PDE estimates and terminal depletion remain external inputs.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 1ℚ; _+_; _-_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst₂)

import DASHI.Physics.Common.WeightedStrictLossTransportExact as Loss

fourClassSteps : ℚ → ℚ → ℚ → ℚ → List Loss.WeightedLossStep
fourClassSteps lowHigh highLow comparable highHigh =
  Loss.weightedLossStep 1ℚ lowHigh
  ∷ Loss.weightedLossStep 1ℚ highLow
  ∷ Loss.weightedLossStep 1ℚ comparable
  ∷ Loss.weightedLossStep 1ℚ highHigh
  ∷ []

fourClassInheritedFloor :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
fourClassInheritedFloor terminal lowHigh highLow comparable highHigh =
  Loss.pullBackFloor terminal
    (fourClassSteps lowHigh highLow comparable highHigh)

fourClassInheritedFloorExact :
  ∀ terminal lowHigh highLow comparable highHigh →
  fourClassInheritedFloor
    terminal lowHigh highLow comparable highHigh
  ≡ terminal - (lowHigh + highLow + comparable + highHigh)
fourClassInheritedFloorExact
    terminal lowHigh highLow comparable highHigh =
  ℚRing.solve-∀ terminal lowHigh highLow comparable highHigh

FourClassStrictBudget :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → Set
FourClassStrictBudget
    margin terminal lowHigh highLow comparable highHigh =
  margin + (lowHigh + highLow + comparable + highHigh)
  ≤ terminal

fourClassStrictBudgetImpliesPositiveFloor :
  ∀ margin terminal lowHigh highLow comparable highHigh →
  FourClassStrictBudget
    margin terminal lowHigh highLow comparable highHigh →
  margin ≤
    fourClassInheritedFloor
      terminal lowHigh highLow comparable highHigh
fourClassStrictBudgetImpliesPositiveFloor
    margin terminal lowHigh highLow comparable highHigh budget =
  let
    steps = fourClassSteps lowHigh highLow comparable highHigh

    leftTransport :
      margin + (lowHigh + highLow + comparable + highHigh)
      ≡ margin + Loss.discountedLoss steps
    leftTransport =
      ℚRing.solve-∀ margin lowHigh highLow comparable highHigh

    rightTransport :
      terminal ≡ Loss.terminalWeight steps * terminal
    rightTransport =
      ℚRing.solve-∀ terminal lowHigh highLow comparable highHigh

    sharedBudget : Loss.StrictMarginAdmissible margin terminal steps
    sharedBudget =
      subst₂ _≤_ leftTransport rightTransport budget
  in
  Loss.strictMarginBelowPullBack
    margin terminal steps sharedBudget
