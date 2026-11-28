module DASHI.Physics.YangMills.YMClayCMP102OriginalFactorialMassBudgetExact where

------------------------------------------------------------------------
-- CMP102 ORIGINAL A/B FACTORIAL COEFFICIENT MASS RECEIVER.
--
-- Consume source coefficients without creating a second analytic
-- series or any infinite geometric partial sum:
--   a_n=1/(2n+2)!, b_n=1/(2n+3)!.
-- On the SOURCE positive factorial ratio 1/12 and 1/20, use
-- the real finite ratio-bank induction:
--   S_n + (12/11)a_n <= 6/11,
--   T_n + (20/19)b_n <= 10/57.
--
-- Ratio proofs are isolated as two named true ORIGINAL factorial
-- order leaves, not asserted as theorems without source evidence.
-- The existing CMP109 proof of coefficient NONNEGATIVITY is reused.
-- The resulting ceiling proof is source-written pending Agda 2.9.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product using (_×_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ; _/_)
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Foundations.BishopFiniteRatioBudgetExact as Budget
import DASHI.Physics.YangMills.BalabanCMP109BishopRootFreeSeriesExact as CMP109
import DASHI.Physics.YangMills.YMClayCMP102OriginalEndpointCauchyShiftExact as Original

ratioA ratioB budgetA budgetB : R.ℝ
ratioA = R._⋆ (+ 1 / 12)
ratioB = R._⋆ (+ 1 / 20)
budgetA = R._⋆ (+ 12 / 11)
budgetB = R._⋆ (+ 20 / 19)

-- THESE TWO SOURCE-SPECIFIC FACTORIAL-ORDER LEAVES, not arbitrary
-- assumptions on a surrogate coefficient family, remain unfilled.
OriginalARatio : Set
OriginalARatio =
  ∀ n → R._≤_
    (Original.aCoefficient (suc n))
    (R._*_ ratioA (Original.aCoefficient n))

OriginalBRatio : Set
OriginalBRatio =
  ∀ n → R._≤_
    (Original.bCoefficient (suc n))
    (R._*_ ratioB (Original.bCoefficient n))

-- Original singleton factorial normal forms. No analytic limits.
OriginalAInitial : Set
OriginalAInitial =
  R._≃_ (Original.aCoefficient 0) (R._⋆ (+ 1 / 2))

OriginalBInitial : Set
OriginalBInitial =
  R._≃_ (Original.bCoefficient 0) (R._⋆ (+ 1 / 6))

-- The two exact fixed-point equalities are purely RATIONAL, so the
-- pinned Bishop real semiring solver proves them without division.
originalAFixedBudget :
  R._≃_ (R._+_ R.1ℝ (R._*_ budgetA ratioA)) budgetA
originalAFixedBudget =
  let open P.ℝ-Solver
  in solve 0
    (Κ 1ℚᵘ ⊕ (Κ (+ 12 / 11) ⊗ Κ (+ 1 / 12))
      ⊜ Κ (+ 12 / 11))
    P.≃-refl

originalBFixedBudget :
  R._≃_ (R._+_ R.1ℝ (R._*_ budgetB ratioB)) budgetB
originalBFixedBudget =
  let open P.ℝ-Solver
  in solve 0
    (Κ 1ℚᵘ ⊕ (Κ (+ 20 / 19) ⊗ Κ (+ 1 / 20))
      ⊜ Κ (+ 20 / 19))
    P.≃-refl

-- Positive budget certificates passed with the source factorial
-- ratios because the numerator/denominator order is not a real
-- decidable linear arithmetic assumption.
OriginalBudgetsNonnegative : Set
OriginalBudgetsNonnegative =
  R.NonNegative budgetA × R.NonNegative budgetB

-- Bound the ACTUAL original A coefficient mass for EVERY count.
originalAAllFiniteMassBelowSixElevenths :
  OriginalARatio → OriginalAInitial →
  R.NonNegative budgetA →
  ∀ count →
  R._≤_ (Seq.SeriesOf Original.aCoefficient count)
    (R._⋆ (+ 6 / 11))
originalAAllFiniteMassBelowSixElevenths ratio initial hbudget count =
  P.≤-respʳ-≃
    (P.≃-trans
      (P.*-congˡ initial)
      (let open P.ℝ-Solver
       in solve 0
         (Κ (+ 12 / 11) ⊗ Κ (+ 1 / 2)
           ⊜ Κ (+ 6 / 11))
         P.≃-refl))
    (Budget.finiteRatioAllPrefixesBounded
      Original.aCoefficient ratioA budgetA
      hbudget CMP109.aNN ratio originalAFixedBudget count)

-- Same original B source, with its sharper 1/20 ratio.
originalBAllFiniteMassBelowTenFiftySevenths :
  OriginalBRatio → OriginalBInitial →
  R.NonNegative budgetB →
  ∀ count →
  R._≤_ (Seq.SeriesOf Original.bCoefficient count)
    (R._⋆ (+ 10 / 57))
originalBAllFiniteMassBelowTenFiftySevenths ratio initial hbudget count =
  P.≤-respʳ-≃
    (P.≃-trans
      (P.*-congˡ initial)
      (let open P.ℝ-Solver
       in solve 0
         (Κ (+ 20 / 19) ⊗ Κ (+ 1 / 6)
           ⊜ Κ (+ 10 / 57))
         P.≃-refl))
    (Budget.finiteRatioAllPrefixesBounded
      Original.bCoefficient ratioB budgetB
      hbudget CMP109.bNN ratio originalBFixedBudget count)
