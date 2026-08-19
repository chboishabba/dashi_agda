module DASHI.Physics.Closure.NSTriadKNIntegratedSignedDangerCostRound92Exact where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Integrated signed danger-cost compiler".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; this is exact finite ordered-field algebra.
--
-- RELATIONSHIP
-- This is the finite algebra immediately upstream of
-- NSTriadKNDeterministicDangerOccupationRound82Exact.  Pointwise negative drift
-- is NOT assumed.  Every time/shell cell is allowed an adverse cost C_i:
--
--      N_i + delta D_i <= C_i.
--
-- Favourable signed/helical cells use C_i = 0.  Adverse cells carry their
-- positive excess into the deterministic occupation budget.  Finite summation
-- gives
--
--      sum N_i + delta sum D_i <= sum C_i.
--
-- Hence if occupation/replenishment pays the total adverse cost, the entire
-- interval has a strict integrated critical estimate even though some cells
-- have positive instantaneous drift.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

record SignedDangerCostCell (delta : ℚ) : Set where
  constructor signed-danger-cost-cell
  field
    netProduction dissipation dangerCost : ℚ
    localCostDominatesDrift :
      netProduction + delta * dissipation ≤ dangerCost

open SignedDangerCostCell public

sumProduction : ∀ {delta} → List (SignedDangerCostCell delta) → ℚ
sumProduction [] = 0ℚ
sumProduction (cell ∷ rest) = netProduction cell + sumProduction rest

sumDissipation : ∀ {delta} → List (SignedDangerCostCell delta) → ℚ
sumDissipation [] = 0ℚ
sumDissipation (cell ∷ rest) = dissipation cell + sumDissipation rest

sumDangerCost : ∀ {delta} → List (SignedDangerCostCell delta) → ℚ
sumDangerCost [] = 0ℚ
sumDangerCost (cell ∷ rest) = dangerCost cell + sumDangerCost rest

finiteIntegratedSignedDangerCost :
  ∀ {delta} (cells : List (SignedDangerCostCell delta)) →
  sumProduction cells + delta * sumDissipation cells
    ≤ sumDangerCost cells
finiteIntegratedSignedDangerCost {delta} [] = ℚP.≤-refl
finiteIntegratedSignedDangerCost {delta} (cell ∷ rest) =
  let
    head = localCostDominatesDrift cell
    tail = finiteIntegratedSignedDangerCost rest
    added = ℚP.+-mono-≤ head tail

    leftMeaning :
      (netProduction cell + delta * dissipation cell)
        + (sumProduction rest + delta * sumDissipation rest)
      ≡ sumProduction (cell ∷ rest)
          + delta * sumDissipation (cell ∷ rest)
    leftMeaning =
      solve
        ( netProduction cell ∷ dissipation cell
        ∷ sumProduction rest ∷ sumDissipation rest ∷ delta ∷ [])
  in
  subst
    (λ left → left ≤ sumDangerCost (cell ∷ rest))
    leftMeaning
    added

record IntegratedDangerCostBudget (delta : ℚ) : Set where
  constructor integrated-danger-cost-budget
  field
    cells : List (SignedDangerCostCell delta)
    escapeBudget : ℚ
    dangerCostPaidByEscape : sumDangerCost cells ≤ escapeBudget

open IntegratedDangerCostBudget public

integratedSignedSurplusPaidByEscape :
  ∀ {delta} (budget : IntegratedDangerCostBudget delta) →
  sumProduction (cells budget) + delta * sumDissipation (cells budget)
    ≤ escapeBudget budget
integratedSignedSurplusPaidByEscape budget =
  ℚP.≤-trans
    (finiteIntegratedSignedDangerCost (cells budget))
    (dangerCostPaidByEscape budget)

zeroCostFavourableCell :
  ∀ {delta net diss} →
  net + delta * diss ≤ 0ℚ →
  SignedDangerCostCell delta
zeroCostFavourableCell {net = net} {diss = diss} favourable =
  signed-danger-cost-cell net diss 0ℚ favourable

round92IntermittentPositiveDriftRepresentedByDangerCost : Bool
round92IntermittentPositiveDriftRepresentedByDangerCost = true

round92FiniteIntegratedSignedDangerCostCompilerClosed : Bool
round92FiniteIntegratedSignedDangerCostCompilerClosed = true

round92PointwiseNegativeDriftRequired : Bool
round92PointwiseNegativeDriftRequired = false

round92FiniteIntegratedSignedDangerCostCompilerClosedIsTrue :
  round92FiniteIntegratedSignedDangerCostCompilerClosed ≡ true
round92FiniteIntegratedSignedDangerCostCompilerClosedIsTrue = refl
