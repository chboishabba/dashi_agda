module DASHI.Physics.Closure.NSTriadKNStrongSixThreeWeightedCellRound89Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- DOI: 10.1007/BF02099744.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Piero D'Ancona.
-- Title: "A Short Proof of Commutator Estimates".
-- DOI: 10.1007/s00041-018-9612-8.
-- Correction DOI: 10.1007/s00041-019-09724-7.
--
-- ROUND89 / TWO-DERIVATIVE WEIGHT ON THE EXISTING SIX-THREE CELL
--
-- The mature SixThreeCommutatorCell already retains its two analytic branches
-- separately.  In particular the first branch satisfies
--
--   B1 <= g_s(d) * M_low * M_out.
--
-- Round89 proves g_s(d) S_d^2 = g_w(d).  Therefore multiplication by the two
-- high-frequency separation powers appearing in the viscous relative-growth
-- coefficient gives
--
--   S_d^2 B1 <= g_w(d) * M_low * M_out.
--
-- This is the exact analytic payment needed by the far-gap viscous route.  No
-- new envelope field is assumed here: the proof consumes the existing
-- `firstBranchBound` of the existing six-three cell.
--
-- IMPORTANT BOUNDARY
-- This theorem does not identify the literal signed HH->low transfer variation
-- with `firstBranchSquared`.  That same-object Fourier/Gram identification is
-- now the remaining physical producer for the far-gap route.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteSixThreeCommutatorBudgetExact as Budget
import DASHI.Physics.Closure.NSTriadKNLuoSixThreeCenteredCommutatorScaleExact as Scale
import DASHI.Physics.Closure.NSTriadKNStrongSixThreeTwoDerivativePaymentRound89Exact as Payment

separationSquare : Budget.SixThreeCommutatorCell → ℚ
separationSquare cell =
  Scale.separationScale (Budget.gap cell)
    * Scale.separationScale (Budget.gap cell)

separationSquareNonnegative :
  (cell : Budget.SixThreeCommutatorCell) →
  0ℚ ≤ separationSquare cell
separationSquareNonnegative cell =
  L2.squareNonnegative (Scale.separationScale (Budget.gap cell))

weightedStrongBranchBelowWeakEnvelope :
  (cell : Budget.SixThreeCommutatorCell) →
  separationSquare cell * Budget.firstBranchSquared cell
  ≤ Budget.weakCellEnvelope cell
weightedStrongBranchBelowWeakEnvelope cell =
  let
    d = Budget.gap cell
    s2 = separationSquare cell
    b1 = Budget.firstBranchSquared cell
    low = Budget.lowCriticalMass cell
    out = Budget.outputMass cell
    gs = Scale.strongBranchSquaredGap d
    gw = Scale.weakBranchSquaredGap d

    weightedRaw :
      s2 * b1 ≤ s2 * (gs * low * out)
    weightedRaw =
      let instance s2NN = nonNegative (separationSquareNonnegative cell)
      in ℚP.*-monoˡ-≤-nonNeg s2 (Budget.firstBranchBound cell)

    rearrangedUpper :
      s2 * (gs * low * out)
      ≡ (gs * s2) * low * out
    rearrangedUpper = solve (s2 ∷ gs ∷ low ∷ out ∷ [])

    scalePayment : gs * s2 ≡ gw
    scalePayment = Payment.strongPaysTwoSeparationPowers d

    paidUpper :
      (gs * s2) * low * out ≡ Budget.weakCellEnvelope cell
    paidUpper rewrite scalePayment = refl

    upperMeaning :
      s2 * (gs * low * out) ≡ Budget.weakCellEnvelope cell
    upperMeaning = trans rearrangedUpper paidUpper
  in
  subst
    (λ upper → s2 * b1 ≤ upper)
    upperMeaning
    weightedRaw

round89ExistingStrongCellPaysTwoDerivativeWeight : Bool
round89ExistingStrongCellPaysTwoDerivativeWeight = true

round89LiteralHHVariationFirstBranchIdentificationConstructed : Bool
round89LiteralHHVariationFirstBranchIdentificationConstructed = false

round89ExistingStrongCellPaysTwoDerivativeWeightIsTrue :
  round89ExistingStrongCellPaysTwoDerivativeWeight ≡ true
round89ExistingStrongCellPaysTwoDerivativeWeightIsTrue = refl

round89LiteralHHVariationFirstBranchIdentificationConstructedIsFalse :
  round89LiteralHHVariationFirstBranchIdentificationConstructed ≡ false
round89LiteralHHVariationFirstBranchIdentificationConstructedIsFalse = refl
