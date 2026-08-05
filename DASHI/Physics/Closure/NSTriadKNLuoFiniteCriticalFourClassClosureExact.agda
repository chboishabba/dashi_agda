module DASHI.Physics.Closure.NSTriadKNLuoFiniteCriticalFourClassClosureExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Jean-Michel Bony; Hajer Bahouri; Jean-Yves Chemin;
-- Raphael Danchin.
-- Bony title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Bahouri--Chemin--Danchin title:
-- "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Compose the round-ten four-class Bony accounting with the corrected
-- critical terminal root
--
--   A_q = sqrt(lambda_q D_q).
--
-- The imported budget continues to expose four independent continuum
-- producer estimates.  This module merely requires that its root field is
-- the critical root rather than sqrt(D_q), and proves the exact 1/64 closure
-- once the summed coefficient times A_q is small.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteBonyFourClassAccountingExact as Bony
import DASHI.Physics.Closure.NSTriadKNLuoCriticalTerminalScaleExact as Critical

record CriticalFourClassClosureData : Set where
  constructor critical-four-class-closure-data
  field
    budget : Bony.FourClassTerminalBudget
    geometry : Critical.CriticalTailGeometry
    budgetUsesCriticalRoot :
      Bony.tailRoot budget ≡ Critical.criticalTailRoot geometry
    shellEnergyNonnegative : 0ℚ ≤ Bony.shellEnergy budget
    coefficientCriticalSmallness :
      Bony.coefficientSum budget * Critical.criticalTailRoot geometry
      ≤ Critical.oneSixtyFourth

open CriticalFourClassClosureData public

criticalFourClassTerminalClosure :
  (closureData : CriticalFourClassClosureData) →
  Bony.totalInteraction (budget closureData)
  ≤ Critical.oneSixtyFourth * Bony.shellEnergy (budget closureData)
criticalFourClassTerminalClosure closureData =
  let
    currentBudget = budget closureData

    assembled :
      Bony.totalInteraction currentBudget
      ≤ Bony.coefficientSum currentBudget
        * Bony.tailRoot currentBudget
        * Bony.shellEnergy currentBudget
    assembled = Bony.fourClassTerminalAssembly currentBudget

    rootAdjusted :
      Bony.coefficientSum currentBudget
        * Bony.tailRoot currentBudget
      ≤ Critical.oneSixtyFourth
    rootAdjusted =
      subst
        (λ root →
          Bony.coefficientSum currentBudget * root
          ≤ Critical.oneSixtyFourth)
        (sym (budgetUsesCriticalRoot closureData))
        (coefficientCriticalSmallness closureData)

    scaled :
      (Bony.coefficientSum currentBudget
        * Bony.tailRoot currentBudget)
        * Bony.shellEnergy currentBudget
      ≤ Critical.oneSixtyFourth * Bony.shellEnergy currentBudget
    scaled =
      let
        instance
          energyIsNonnegative =
            nonNegative (shellEnergyNonnegative closureData)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (Bony.shellEnergy currentBudget)
        rootAdjusted
  in
  ℚₚ.≤-trans assembled scaled
