module DASHI.Physics.Closure.NSTriadKNClassNormBudgetToBonyGramPaymentRound582Exact where

------------------------------------------------------------------------
-- ROUND582 / CLASS NORM BUDGETS PAY R580 GRAM RESIDUALS AUTOMATICALLY
--
-- R580 asks for quantitative upper bounds on four classwise signed Gram debts.
-- That is deliberately weaker than a new covariance theorem.  R180 already
-- owns the exact finite identity
--
--   ||sum cells||^2 = cellMassSum cells + gramDebt cells.
--
-- Since every rational C3 cell mass is nonnegative,
--
--   gramDebt cells <= ||sum cells||^2.
--
-- Therefore ANY independently proved class norm/operator budget
--
--   ||sum cells||^2 <= B
--
-- automatically supplies the R580 residual payment with residual B.  This is
-- the least-prerequisite BIDI needed to reuse existing Schur/Young/classwise
-- norm producers; no direct covariance-sign theorem is mandatory.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNFourSignBonyClassGramCompilerRound580Exact as R580
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

cellMassSumNonnegative582 :
  (cells : List (C3.Complex3 F)) →
  0ℚ ≤ R180.cellMassSum cells
cellMassSumNonnegative582 [] = ℚP.≤-refl
cellMassSumNonnegative582 (cell ∷ rest) =
  Rational.addNonnegative
    (Separation.complex3NormSquaredNonnegative cell)
    (cellMassSumNonnegative582 rest)

gramDebtBelowSummedNorm582 :
  (cells : List (C3.Complex3 F)) →
  R180.gramDebt cells
  ≤ L2.complex3NormSquared (R180.sumCells cells)
gramDebtBelowSummedNorm582 cells =
  let
    mass = R180.cellMassSum cells
    debt = R180.gramDebt cells

    zeroPlusDebtBelow :
      0ℚ + debt ≤ mass + debt
    zeroPlusDebtBelow =
      ℚP.+-mono-≤ (cellMassSumNonnegative582 cells) ℚP.≤-refl

    debtBelowMassPlusDebt : debt ≤ mass + debt
    debtBelowMassPlusDebt =
      subst
        (λ lower → lower ≤ mass + debt)
        (ℚP.+-identityˡ debt)
        zeroPlusDebtBelow
  in
  subst
    (debt ≤_)
    (sym (R180.finiteFibreGramLedger cells))
    debtBelowMassPlusDebt

record ClassNormBudget582 (cells : List (C3.Complex3 F)) : Set where
  constructor class-norm-budget-582
  field
    classNormCeiling582 : ℚ
    classSummedNormBound582 :
      L2.complex3NormSquared (R180.sumCells cells)
      ≤ classNormCeiling582

open ClassNormBudget582 public

classNormBudgetPaysGram582 :
  (cells : List (C3.Complex3 F)) →
  (budget : ClassNormBudget582 cells) →
  R180.gramDebt cells ≤ classNormCeiling582 budget
classNormBudgetPaysGram582 cells budget =
  ℚP.≤-trans
    (gramDebtBelowSummedNorm582 cells)
    (classSummedNormBound582 budget)

record FourBonyClassNormBudgets582 (cells : R580.FourBonyClassCells580) : Set where
  constructor four-bony-class-norm-budgets-582
  field
    lowHighNormBudget582 : ClassNormBudget582 (R580.lowHigh580 cells)
    highLowNormBudget582 : ClassNormBudget582 (R580.highLow580 cells)
    highHighToLowNormBudget582 :
      ClassNormBudget582 (R580.highHighToLow580 cells)
    comparableNormBudget582 : ClassNormBudget582 (R580.comparable580 cells)

open FourBonyClassNormBudgets582 public

fourClassNormBudgetsBuildR580Payment582 :
  (cells : R580.FourBonyClassCells580) →
  FourBonyClassNormBudgets582 cells →
  R580.FourBonyClassGramPayment580 cells
fourClassNormBudgetsBuildR580Payment582 cells budgets =
  R580.four-bony-class-gram-payment-580
    (classNormCeiling582 (lowHighNormBudget582 budgets))
    (classNormCeiling582 (highLowNormBudget582 budgets))
    (classNormCeiling582 (highHighToLowNormBudget582 budgets))
    (classNormCeiling582 (comparableNormBudget582 budgets))
    (classNormBudgetPaysGram582
      (R580.lowHigh580 cells) (lowHighNormBudget582 budgets))
    (classNormBudgetPaysGram582
      (R580.highLow580 cells) (highLowNormBudget582 budgets))
    (classNormBudgetPaysGram582
      (R580.highHighToLow580 cells) (highHighToLowNormBudget582 budgets))
    (classNormBudgetPaysGram582
      (R580.comparable580 cells) (comparableNormBudget582 budgets))

------------------------------------------------------------------------
-- Status / proof-search reduction.
------------------------------------------------------------------------

round582CellMassNonnegativeClosed : Bool
round582CellMassNonnegativeClosed = true

round582GramDebtBelowClassNormClosed : Bool
round582GramDebtBelowClassNormClosed = true

round582FourClassNormBudgetsBuildR580Payment : Bool
round582FourClassNormBudgetsBuildR580Payment = true

round582DirectCovarianceTheoremMandatory : Bool
round582DirectCovarianceTheoremMandatory = false

round582AnyLiteralClassNormBudgetConstructed : Bool
round582AnyLiteralClassNormBudgetConstructed = false

round582OuterSpectatorWeightedSpacetimeBoundClosed : Bool
round582OuterSpectatorWeightedSpacetimeBoundClosed = false

round582CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round582CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round582ClayPromotion : Bool
round582ClayPromotion = false

round582GramDebtBelowClassNormClosedIsTrue :
  round582GramDebtBelowClassNormClosed ≡ true
round582GramDebtBelowClassNormClosedIsTrue = refl

round582DirectCovarianceTheoremMandatoryIsFalse :
  round582DirectCovarianceTheoremMandatory ≡ false
round582DirectCovarianceTheoremMandatoryIsFalse = refl

round582ClayPromotionIsFalse : round582ClayPromotion ≡ false
round582ClayPromotionIsFalse = refl
