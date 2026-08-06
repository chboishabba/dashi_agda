module DASHI.Physics.Closure.NSTriadKNLuoPeriodicGalerkinFourClassContinuationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Jean-Michel Bony; Hajer Bahouri; Jean-Yves Chemin;
-- Raphael Danchin.
-- Bony DOI: 10.24033/asens.1404.
-- Bahouri--Chemin--Danchin DOI: 10.1007/978-3-642-16830-7.
--
-- Author: James Serrin.
-- Title: "On the Interior Regularity of Weak Solutions of the Navier--Stokes
-- Equations".
-- DOI: 10.1007/BF00253344.
--
-- Author: Terence Tao.
-- Title: "254A, Notes 1: Local Well-Posedness of the Navier-Stokes
-- Equations".
-- DOI: not assigned.
--
-- PURPOSE
-- Turn the radical-free four-class estimate into the exact 1/64 terminal
-- threshold at the squared level. If
--
--   4 C_sum A_q^2 <= 1/4096,
--
-- then
--
--   N_q^2 <= (1/4096) E_q^2.
--
-- This is the precise conditional continuation criterion. It does not claim
-- that the critical smallness hypothesis is automatic.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _/_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoRound14SquaredFourClassClosureExact as FourClass

oneOver4096 : ℚ
oneOver4096 = Int.+ 1 / 4096

record PeriodicGalerkinContinuationBudget : Set where
  constructor periodic-galerkin-continuation-budget
  field
    fourClassBudget : FourClass.SquaredFourClassBudget

    outputEnvelopeSquaredNonnegative :
      0ℚ ≤ FourClass.outputEnvelopeSquared fourClassBudget

    criticalCoefficientSmallness :
      FourClass.four
        * (FourClass.coefficientSum fourClassBudget
          * FourClass.criticalEnvelopeSquared fourClassBudget)
      ≤ oneOver4096

open PeriodicGalerkinContinuationBudget public

periodicGalerkinTerminalSmallnessSquared :
  (dataSet : PeriodicGalerkinContinuationBudget) →
  L2.square
    (FourClass.totalInteraction (fourClassBudget dataSet))
  ≤ oneOver4096
    * FourClass.outputEnvelopeSquared (fourClassBudget dataSet)
periodicGalerkinTerminalSmallnessSquared dataSet =
  let
    assembled =
      FourClass.squaredFourClassTerminalAssembly
        (fourClassBudget dataSet)

    coefficientTimesOutput :
      FourClass.four
        * (FourClass.coefficientSum (fourClassBudget dataSet)
          * FourClass.criticalEnvelopeSquared (fourClassBudget dataSet))
        * FourClass.outputEnvelopeSquared (fourClassBudget dataSet)
      ≤ oneOver4096
        * FourClass.outputEnvelopeSquared (fourClassBudget dataSet)
    coefficientTimesOutput =
      let
        instance
          outputNN =
            nonNegative (outputEnvelopeSquaredNonnegative dataSet)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (FourClass.outputEnvelopeSquared (fourClassBudget dataSet))
        (criticalCoefficientSmallness dataSet)

    assembledMeaning :
      FourClass.four
        * (FourClass.coefficientSum (fourClassBudget dataSet)
          * FourClass.criticalEnvelopeSquared (fourClassBudget dataSet)
          * FourClass.outputEnvelopeSquared (fourClassBudget dataSet))
      ≡ FourClass.four
        * (FourClass.coefficientSum (fourClassBudget dataSet)
          * FourClass.criticalEnvelopeSquared (fourClassBudget dataSet))
        * FourClass.outputEnvelopeSquared (fourClassBudget dataSet)
    assembledMeaning =
      solve
        ( FourClass.coefficientSum (fourClassBudget dataSet)
        ∷ FourClass.criticalEnvelopeSquared (fourClassBudget dataSet)
        ∷ FourClass.outputEnvelopeSquared (fourClassBudget dataSet)
        ∷ [])
  in
  ℚₚ.≤-trans
    assembled
    (subst
      (λ lower →
        lower
        ≤ oneOver4096
          * FourClass.outputEnvelopeSquared (fourClassBudget dataSet))
      (sym assembledMeaning)
      coefficientTimesOutput)

oneOver4096IsOneOver64Squared :
  oneOver4096 ≡ (Int.+ 1 / 64) * (Int.+ 1 / 64)
oneOver4096IsOneOver64Squared = solve []
