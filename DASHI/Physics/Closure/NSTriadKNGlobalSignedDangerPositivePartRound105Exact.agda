module DASHI.Physics.Closure.NSTriadKNGlobalSignedDangerPositivePartRound105Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND105 / GLOBAL SIGNED DANGER PAYMENT
--
-- Round92 permits a positive danger cost C_i for every time/shell cell and
-- then sums those costs.  That is safe, but it can throw away exactly the
-- cancellation which Rounds102--104 preserve in the complete signed critical
-- production.
--
-- The sharp finite algebraic payment is instead applied AFTER summation:
--
--   surplus = sum_i N_i + delta sum_i D_i,
--   globalDanger = surplus_+ = (|surplus| + surplus)/2.
--
-- Then
--
--   surplus <= globalDanger,
--
-- while globalDanger is nonnegative.  Hence a physical theorem only needs to
-- pay the positive part of the COMPLETE integrated signed surplus.  It does
-- not need to pay the sum of positive parts of independently majorised cells.
--
-- This is a strict abstraction improvement: all cross-shell, cross-triad and
-- cross-time cancellation remains available until the final one-dimensional
-- order operation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; ∣_∣; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNIntegratedSignedDangerCostRound92Exact as Round92

half : ℚ
half = + 1 / 2

halfNonnegative : 0ℚ ≤ half
halfNonnegative = ℚP.<⇒≤ (ℚP.positive⁻¹ half)

positivePart : ℚ → ℚ
positivePart x = half * (∣ x ∣ + x)

positivePartDominates : (x : ℚ) → x ≤ positivePart x
positivePartDominates x =
  let
    xBelowAbs : x ≤ ∣ x ∣
    xBelowAbs = ℚP.p≤∣p∣ x

    doubledBelow : x + x ≤ ∣ x ∣ + x
    doubledBelow = ℚP.+-mono-≤ xBelowAbs ℚP.≤-refl

    scaled : half * (x + x) ≤ half * (∣ x ∣ + x)
    scaled =
      let instance halfNN : NonNegative half
          halfNN = nonNegative halfNonnegative
      in ℚP.*-monoˡ-≤-nonNeg half doubledBelow

    leftMeaning : half * (x + x) ≡ x
    leftMeaning = solve (x ∷ [])
  in
  subst (λ left → left ≤ positivePart x) leftMeaning scaled

positivePartNonnegative : (x : ℚ) → 0ℚ ≤ positivePart x
positivePartNonnegative x =
  let
    negAbsBelowX : 0ℚ + (0ℚ - ∣ x ∣) ≤ 0ℚ + x
    negAbsBelowX = ℚP.+-mono-≤ ℚP.≤-refl (ℚP.-∣p∣≤p x)

    absPlusXNN : 0ℚ ≤ ∣ x ∣ + x
    absPlusXNN =
      subst
        (λ left → left ≤ ∣ x ∣ + x)
        (solve (∣ x ∣ ∷ []))
        (subst
          (λ right → 0ℚ + (0ℚ - ∣ x ∣) ≤ right)
          (solve (∣ x ∣ ∷ x ∷ []))
          negAbsBelowX)

    scaled : half * 0ℚ ≤ half * (∣ x ∣ + x)
    scaled =
      let instance halfNN : NonNegative half
          halfNN = nonNegative halfNonnegative
      in ℚP.*-monoˡ-≤-nonNeg half absPlusXNN
  in
  subst (λ left → left ≤ positivePart x) (solve []) scaled

integratedSurplus :
  ∀ {delta} → List (Round92.SignedDangerCostCell delta) → ℚ
integratedSurplus {delta} cells =
  Round92.sumProduction cells + delta * Round92.sumDissipation cells

globalDangerCost :
  ∀ {delta} → List (Round92.SignedDangerCostCell delta) → ℚ
globalDangerCost cells = positivePart (integratedSurplus cells)

globalDangerCostDominatesIntegratedSurplus :
  ∀ {delta} (cells : List (Round92.SignedDangerCostCell delta)) →
  integratedSurplus cells ≤ globalDangerCost cells
globalDangerCostDominatesIntegratedSurplus cells =
  positivePartDominates (integratedSurplus cells)

globalDangerCostNonnegative :
  ∀ {delta} (cells : List (Round92.SignedDangerCostCell delta)) →
  0ℚ ≤ globalDangerCost cells
globalDangerCostNonnegative cells =
  positivePartNonnegative (integratedSurplus cells)

record GlobalSignedDangerBudget (delta : ℚ) : Set where
  constructor global-signed-danger-budget
  field
    cells : List (Round92.SignedDangerCostCell delta)
    escapeBudget : ℚ
    globalDangerPaidByEscape : globalDangerCost cells ≤ escapeBudget

open GlobalSignedDangerBudget public

globalSignedSurplusPaidByEscape :
  ∀ {delta} (budget : GlobalSignedDangerBudget delta) →
  Round92.sumProduction (cells budget)
    + delta * Round92.sumDissipation (cells budget)
  ≤ escapeBudget budget
globalSignedSurplusPaidByEscape budget =
  ℚP.≤-trans
    (globalDangerCostDominatesIntegratedSurplus (cells budget))
    (globalDangerPaidByEscape budget)

------------------------------------------------------------------------
-- Comparison boundary.
--
-- Round92's local-cost compiler is still useful when local estimates are all
-- that are available.  Round105 shows it is not the mathematically minimal
-- consumer.  The highest-alpha physical theorem should target globalDangerCost
-- directly whenever the complete signed packet layer-cake is available.
------------------------------------------------------------------------

round105GlobalSignedPositivePartPaymentClosed : Bool
round105GlobalSignedPositivePartPaymentClosed = true

round105PerCellPositiveTaxRequired : Bool
round105PerCellPositiveTaxRequired = false

round105PhysicalGlobalDangerPaymentClosed : Bool
round105PhysicalGlobalDangerPaymentClosed = false

round105GlobalSignedPositivePartPaymentClosedIsTrue :
  round105GlobalSignedPositivePartPaymentClosed ≡ true
round105GlobalSignedPositivePartPaymentClosedIsTrue = refl

round105PerCellPositiveTaxRequiredIsFalse :
  round105PerCellPositiveTaxRequired ≡ false
round105PerCellPositiveTaxRequiredIsFalse = refl

round105PhysicalGlobalDangerPaymentClosedIsFalse :
  round105PhysicalGlobalDangerPaymentClosed ≡ false
round105PhysicalGlobalDangerPaymentClosedIsFalse = refl
