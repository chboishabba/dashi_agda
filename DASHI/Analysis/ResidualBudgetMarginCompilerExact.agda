module DASHI.Analysis.ResidualBudgetMarginCompilerExact where

------------------------------------------------------------------------
-- GENERIC RESIDUAL-BUDGET / STRICT-MARGIN COMPILER
--
-- This is the domain-neutral theorem shape shared by:
--
--   * G21 determinant-level Taylor transfer;
--   * Aristotle's current narrow-window Schur admission gate; and
--   * the Round202 Navier--Stokes positive-Gram-debt residual-budget pattern.
--
-- A residual need not be negative, vanish, or have a favourable sign.
-- It is enough to prove
--
--     residual <= budget < strictSignalMargin.
--
-- Then the residual lies strictly below the signal margin.
--
-- This deliberately separates
--
--     exact/signed algebra
--
-- from
--
--     quantitative payment.
--
-- No RH, Navier--Stokes or other domain theorem follows merely from this
-- compiler.  Domain owners must still inhabit the residual-bound and strict-
-- margin hypotheses with their literal quantities.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP

record ResidualBudgetMargin : Set where
  constructor residual-budget-margin
  field
    residual budget strictSignalMargin : ℚ
    residualBound : residual ≤ budget
    budgetBelowStrictMargin : budget < strictSignalMargin

open ResidualBudgetMargin public

residualStrictlyBelowSignalMargin :
  (d : ResidualBudgetMargin) → residual d < strictSignalMargin d
residualStrictlyBelowSignalMargin d =
  ℚP.≤-<-trans (residualBound d) (budgetBelowStrictMargin d)

------------------------------------------------------------------------
-- The same compiler with two separately controlled residual groups.  This is
-- the shape used when one wants to keep, for example, a structured/local
-- residual and a far-tail residual separately visible until the final gate.
------------------------------------------------------------------------

record SplitResidualBudgetMargin : Set where
  constructor split-residual-budget-margin
  field
    structuredResidual farResidual : ℚ
    structuredBudget farBudget strictSignalMargin : ℚ
    structuredBound : structuredResidual ≤ structuredBudget
    farBound : farResidual ≤ farBudget
    combinedBudgetBelowStrictMargin :
      structuredBudget + farBudget < strictSignalMargin

open SplitResidualBudgetMargin public

splitResidualStrictlyBelowSignalMargin :
  (d : SplitResidualBudgetMargin) →
  structuredResidual d + farResidual d < strictSignalMargin d
splitResidualStrictlyBelowSignalMargin d =
  ℚP.≤-<-trans
    (ℚP.+-mono-≤ (structuredBound d) (farBound d))
    (combinedBudgetBelowStrictMargin d)

record ResidualBudgetMarginBoundary : Set where
  constructor residual-budget-margin-boundary
  field
    residualMustBeNonPositive : Bool
    residualMustBeNonPositiveIsFalse : residualMustBeNonPositive ≡ false
    directMarginComparisonPreferred : Bool
    directMarginComparisonPreferredIsTrue : directMarginComparisonPreferred ≡ true
    domainClaimDerivedByCompilerAlone : Bool
    domainClaimDerivedByCompilerAloneIsFalse : domainClaimDerivedByCompilerAlone ≡ false

canonicalResidualBudgetMarginBoundary : ResidualBudgetMarginBoundary
canonicalResidualBudgetMarginBoundary =
  residual-budget-margin-boundary false refl true refl false refl
