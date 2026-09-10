module DASHI.Physics.Closure.NSTriadKNExactBonyClassNormSelfBudgetBidiExact where

------------------------------------------------------------------------
-- EXACT SELF-BUDGETS FOR THE R582/R583 BONY CLASS-NORM INTERFACE
--
-- R582's ClassNormBudget582 asks only for some ceiling B with
--
--   ||sum cells||^2 <= B.
--
-- Therefore existence of a budget is not analytic debt: choose the exact norm
-- itself as the ceiling and discharge the inequality by reflexivity.  The real
-- theorem-bearing task is to majorize these exact finite class norms by a
-- useful cutoff-uniform / spacetime envelope.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNFourSignBonyClassGramCompilerRound580Exact as R580
import DASHI.Physics.Closure.NSTriadKNClassNormBudgetToBonyGramPaymentRound582Exact as R582

F : C3.RealField _
F = Rational.rationalRealField

exactClassNormSelfBudget :
  (cells : List (C3.Complex3 F)) →
  R582.ClassNormBudget582 cells
exactClassNormSelfBudget cells =
  R582.class-norm-budget-582
    (L2.complex3NormSquared (R180.sumCells cells))
    ℚP.≤-refl

exactFourBonyClassSelfBudgets :
  (cells : R580.FourBonyClassCells580) →
  R582.FourBonyClassNormBudgets582 cells
exactFourBonyClassSelfBudgets cells =
  R582.four-bony-class-norm-budgets-582
    (exactClassNormSelfBudget (R580.lowHigh580 cells))
    (exactClassNormSelfBudget (R580.highLow580 cells))
    (exactClassNormSelfBudget (R580.highHighToLow580 cells))
    (exactClassNormSelfBudget (R580.comparable580 cells))

classBudgetExistenceIsCompilerOwned : Bool
classBudgetExistenceIsCompilerOwned = true

usefulUniformClassNormEnvelopeConstructedHere : Bool
usefulUniformClassNormEnvelopeConstructedHere = false

classBudgetExistenceIsCompilerOwnedIsTrue :
  classBudgetExistenceIsCompilerOwned ≡ true
classBudgetExistenceIsCompilerOwnedIsTrue = refl

usefulUniformClassNormEnvelopeConstructedHereIsFalse :
  usefulUniformClassNormEnvelopeConstructedHere ≡ false
usefulUniformClassNormEnvelopeConstructedHereIsFalse = refl
