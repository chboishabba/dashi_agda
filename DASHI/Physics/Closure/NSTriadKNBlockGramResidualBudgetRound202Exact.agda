module DASHI.Physics.Closure.NSTriadKNBlockGramResidualBudgetRound202Exact where

------------------------------------------------------------------------
-- ROUND202 / POSITIVE GRAM DEBT IS ALLOWED: QUANTITATIVE RESIDUAL BUDGET
--
-- Round183 already proves that a generic between-partner Gram debt can be
-- positive.  Therefore the old sufficient condition `GramDebt <= 0` is too
-- strong to serve as the arbitrary-data discovery target.
--
-- Round201 gives the exact block identity
--
--   ||Σ_a S_a||² = M_cells + D_within + D_between.
--
-- The correct analytic contract is consequently quantitative, not a sign
-- theorem.  If
--
--   D_within  <= W,
--   D_between <= B,
--
-- then exactly
--
--   ||Σ_a S_a||² <= M_cells + W + B.
--
-- W and B may be positive.  The physical FL / HH / CC estimates only need to
-- make their aggregate residual budgets cutoff-uniform and absorbable in the
-- quartic companion; they do NOT need to manufacture false Gram negativity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNBlockGramCovarianceTelescopeRound201Exact as R201

record BlockResidualBudget (blocks : List R201.SignedBlock) : Set where
  constructor block-residual-budget
  field
    withinBudget betweenBudget : ℚ
    withinDebtBound : R201.withinBlockGramDebt blocks ≤ withinBudget
    betweenDebtBound : R201.betweenBlockGramDebt blocks ≤ betweenBudget

open BlockResidualBudget public

blockResidualBudgetClosesGroupedMass :
  (blocks : List R201.SignedBlock) →
  (budget : BlockResidualBudget blocks) →
  L2.complex3NormSquared (R201.groupedBlockSum blocks)
  ≤ R201.cellMassAcrossBlocks blocks
      + withinBudget budget
      + betweenBudget budget
blockResidualBudgetClosesGroupedMass blocks budget =
  let
    debtBound :
      R201.cellMassAcrossBlocks blocks
        + R201.withinBlockGramDebt blocks
        + R201.betweenBlockGramDebt blocks
      ≤ R201.cellMassAcrossBlocks blocks
        + withinBudget budget
        + betweenBudget budget
    debtBound =
      ℚP.+-mono-≤
        (ℚP.+-mono-≤ ℚP.≤-refl (withinDebtBound budget))
        (betweenDebtBound budget)
  in
  subst
    (λ left →
      left ≤ R201.cellMassAcrossBlocks blocks
        + withinBudget budget
        + betweenBudget budget)
    (R201.blockGramCovarianceTelescope blocks)
    debtBound

-- Sometimes the physical estimate naturally controls only the sum of the two
-- residual debts.  Keep that contract separately so no artificial split is
-- required by downstream code.
record TotalBlockResidualBudget (blocks : List R201.SignedBlock) : Set where
  constructor total-block-residual-budget
  field
    residualBudget : ℚ
    totalDebtBound :
      R201.withinBlockGramDebt blocks + R201.betweenBlockGramDebt blocks
      ≤ residualBudget

open TotalBlockResidualBudget public

totalResidualBudgetClosesGroupedMass :
  (blocks : List R201.SignedBlock) →
  (budget : TotalBlockResidualBudget blocks) →
  L2.complex3NormSquared (R201.groupedBlockSum blocks)
  ≤ R201.cellMassAcrossBlocks blocks + residualBudget budget
totalResidualBudgetClosesGroupedMass blocks budget =
  let
    mass = R201.cellMassAcrossBlocks blocks
    within = R201.withinBlockGramDebt blocks
    between = R201.betweenBlockGramDebt blocks

    regrouped :
      mass + within + between ≡ mass + (within + between)
    regrouped = solve (mass ∷ within ∷ between ∷ [])

    shifted :
      mass + (within + between) ≤ mass + residualBudget budget
    shifted = ℚP.+-monoʳ-≤ mass (totalDebtBound budget)

    debtBound :
      mass + within + between ≤ mass + residualBudget budget
    debtBound = subst
      (λ left → left ≤ mass + residualBudget budget)
      (sym regrouped)
      shifted
  in
  subst
    (λ left → left ≤ mass + residualBudget budget)
    (R201.blockGramCovarianceTelescope blocks)
    debtBound

round202GramNegativityRequired : Bool
round202GramNegativityRequired = false

round202PositiveResidualCovarianceAdmissible : Bool
round202PositiveResidualCovarianceAdmissible = true

round202QuantitativeBlockResidualCompilerClosed : Bool
round202QuantitativeBlockResidualCompilerClosed = true

round202PhysicalFLResidualBudgetClosed : Bool
round202PhysicalFLResidualBudgetClosed = false

round202PhysicalHHResidualBudgetClosed : Bool
round202PhysicalHHResidualBudgetClosed = false

round202PhysicalCCResidualBudgetClosed : Bool
round202PhysicalCCResidualBudgetClosed = false

round202PackageAClosed : Bool
round202PackageAClosed = false

round202ClayPromotion : Bool
round202ClayPromotion = false

round202GramNegativityRequiredIsFalse : round202GramNegativityRequired ≡ false
round202GramNegativityRequiredIsFalse = refl

round202QuantitativeBlockResidualCompilerClosedIsTrue :
  round202QuantitativeBlockResidualCompilerClosed ≡ true
round202QuantitativeBlockResidualCompilerClosedIsTrue = refl

round202PackageAClosedIsFalse : round202PackageAClosed ≡ false
round202PackageAClosedIsFalse = refl
