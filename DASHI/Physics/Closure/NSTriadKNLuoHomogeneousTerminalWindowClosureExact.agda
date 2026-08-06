module DASHI.Physics.Closure.NSTriadKNLuoHomogeneousTerminalWindowClosureExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Repository-original exact closure interface; no DOI is assigned.
--
-- Related harmonic-analysis reference:
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Replace the amplitude-inhomogeneous quartic target
--
--   interaction <= C * D_q * E_q
--
-- by the degree-compatible conditional interface
--
--   interaction <= C * sqrt(D_q) * E_q.
--
-- Rather than postulating a square-root operation on constructive reals, the
-- finite carrier supplies a nonnegative root together with the exact equation
-- tailMass = tailRoot^2.  The four Bony-class estimates remain explicit fields
-- of the imported budget.  Once
--
--   coefficientSum * tailRoot <= 1/64,
--
-- the total interaction is at most (1/64) shellEnergy.
--
-- This module proves the composition only.  It does not claim that energy,
-- dissipation and incompressibility produce the four classwise estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _/_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteBonyFourClassAccountingExact as Bony

oneSixtyFourth : ℚ
oneSixtyFourth = Int.+ 1 / 64

record RootedDissipationTail : Set where
  constructor rooted-dissipation-tail
  field
    tailRoot tailMass : ℚ
    tailRootNonnegative : 0ℚ ≤ tailRoot
    tailMassNonnegative : 0ℚ ≤ tailMass
    tailMassIsSquare : tailMass ≡ tailRoot * tailRoot

open RootedDissipationTail public

record HomogeneousTerminalClosureData : Set where
  constructor homogeneous-terminal-closure-data
  field
    budget : Bony.FourClassTerminalBudget
    rootedTail : RootedDissipationTail
    budgetUsesRoot :
      Bony.tailRoot budget ≡ tailRoot rootedTail
    shellEnergyNonnegative : 0ℚ ≤ Bony.shellEnergy budget
    coefficientRootSmallness :
      Bony.coefficientSum budget * tailRoot rootedTail
      ≤ oneSixtyFourth

open HomogeneousTerminalClosureData public

homogeneousTerminalWindowClosure :
  (closureData : HomogeneousTerminalClosureData) →
  Bony.totalInteraction (budget closureData)
  ≤ oneSixtyFourth * Bony.shellEnergy (budget closureData)
homogeneousTerminalWindowClosure closureData =
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
      ≤ oneSixtyFourth
    rootAdjusted =
      subst
        (λ root →
          Bony.coefficientSum currentBudget * root
          ≤ oneSixtyFourth)
        (sym (budgetUsesRoot closureData))
        (coefficientRootSmallness closureData)

    scaled :
      (Bony.coefficientSum currentBudget
        * Bony.tailRoot currentBudget)
        * Bony.shellEnergy currentBudget
      ≤ oneSixtyFourth * Bony.shellEnergy currentBudget
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
