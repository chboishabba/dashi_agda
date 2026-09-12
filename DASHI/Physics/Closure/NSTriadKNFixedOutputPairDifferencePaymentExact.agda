module DASHI.Physics.Closure.NSTriadKNFixedOutputPairDifferencePaymentExact where

------------------------------------------------------------------------
-- P3 COMPILER / LOWER PARTNER SEPARATION PAYS SAME-OUTPUT GRAM DEBT
--
-- P1 proves on the literal R207 fixed-output carrier
--
--   debt + PairDiffMass = (n - 1) * cellMass.
--
-- P2 identifies PairDiffMass with the complete finite sum of the literal R574
-- partner-difference norm squares.  Therefore the only physical premise needed
-- to pay the same-output debt by a residual R is
--
--   (n - 1) * cellMass - R <= PairDiffMass.
--
-- This owner proves the rational-order consequence
--
--   debt <= R.
--
-- No lower-separation estimate is manufactured here.  In particular radial,
-- angular, Pluecker, centered-moment, shell, cutoff and spacetime inputs remain
-- entirely upstream of this compiler.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as YMSums
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNComparableFixedOutputCarrierRound207Exact as R207
import DASHI.Physics.Closure.NSTriadKNFixedOutputPairDifferenceDebtExact as P1
import DASHI.Physics.Closure.NSTriadKNFixedOutputPairDifferenceAggregateExact as P2

F = P1.F

fixedOutputPairDifferenceLowerPaysDebt :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {output : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode}
    (entries : List (R207.FixedOutputLocalizedComparablePartner system output))
    (residualBudget : ℚ) →
  (YMSums.natAsRational (length (R207.fixedOutputPartnerCells entries)) - 1ℚ)
      * R180.cellMassSum (R207.fixedOutputPartnerCells entries)
      - residualBudget
    ≤ P1.fixedOutputPairDifferenceMass entries →
  R207.fixedOutputBetweenPartnerDebt entries ≤ residualBudget
fixedOutputPairDifferenceLowerPaysDebt entries residualBudget lowerPayment =
  let
    debt = R207.fixedOutputBetweenPartnerDebt entries
    pairDiff = P1.fixedOutputPairDifferenceMass entries
    total =
      (YMSums.natAsRational (length (R207.fixedOutputPartnerCells entries)) - 1ℚ)
        * R180.cellMassSum (R207.fixedOutputPartnerCells entries)

    addResidual :
      (total - residualBudget) + residualBudget
      ≤ pairDiff + residualBudget
    addResidual = ℚP.+-mono-≤ lowerPayment ℚP.≤-refl

    totalBelowPairPlusResidual :
      total ≤ pairDiff + residualBudget
    totalBelowPairPlusResidual =
      subst
        (λ left → left ≤ pairDiff + residualBudget)
        (solve (total ∷ residualBudget ∷ []))
        addResidual

    debtPlusPairBelow :
      debt + pairDiff ≤ pairDiff + residualBudget
    debtPlusPairBelow =
      subst
        (λ left → left ≤ pairDiff + residualBudget)
        (sym (P1.fixedOutputDebtPlusPairDifference entries))
        totalBelowPairPlusResidual

    pairPlusDebtBelow :
      pairDiff + debt ≤ pairDiff + residualBudget
    pairPlusDebtBelow =
      subst
        (λ left → left ≤ pairDiff + residualBudget)
        (ℚP.+-comm debt pairDiff)
        debtPlusPairBelow
  in
  ℚP.+-cancelˡ-≤ pairDiff pairPlusDebtBelow

fixedOutputR574LowerPaysDebt :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {output : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode}
    (entries : List (R207.FixedOutputLocalizedComparablePartner system output))
    (residualBudget : ℚ)
    (rate : ℚ)
    (ratePositive : Data.Rational.Base.Positive rate) →
  (YMSums.natAsRational (length (R207.fixedOutputPartnerCells entries)) - 1ℚ)
      * R180.cellMassSum (R207.fixedOutputPartnerCells entries)
      - residualBudget
    ≤ P2.r574PairNormMass rate ratePositive entries →
  R207.fixedOutputBetweenPartnerDebt entries ≤ residualBudget
fixedOutputR574LowerPaysDebt entries residualBudget rate ratePositive lowerR574 =
  fixedOutputPairDifferenceLowerPaysDebt entries residualBudget
    (subst
      (λ right →
        (YMSums.natAsRational (length (R207.fixedOutputPartnerCells entries)) - 1ℚ)
          * R180.cellMassSum (R207.fixedOutputPartnerCells entries)
          - residualBudget
        ≤ right)
      (sym (P2.fixedOutputPairDifferenceMassIsR574PairNormMass
        rate ratePositive entries))
      lowerR574)

------------------------------------------------------------------------
-- Status: all Gram/order bookkeeping closed; physical lower separation open.
------------------------------------------------------------------------

fixedOutputPairDifferencePaymentCompilerClosed : Bool
fixedOutputPairDifferencePaymentCompilerClosed = true

fixedOutputPairDifferencePaymentUsesLiteralR574Aggregate : Bool
fixedOutputPairDifferencePaymentUsesLiteralR574Aggregate = true

fixedOutputPhysicalLowerSeparationClosed : Bool
fixedOutputPhysicalLowerSeparationClosed = false

fixedOutputPairDifferencePaymentClayPromotion : Bool
fixedOutputPairDifferencePaymentClayPromotion = false

fixedOutputPairDifferencePaymentCompilerClosedIsTrue :
  fixedOutputPairDifferencePaymentCompilerClosed ≡ true
fixedOutputPairDifferencePaymentCompilerClosedIsTrue = refl

fixedOutputPhysicalLowerSeparationClosedIsFalse :
  fixedOutputPhysicalLowerSeparationClosed ≡ false
fixedOutputPhysicalLowerSeparationClosedIsFalse = refl

fixedOutputPairDifferencePaymentClayPromotionIsFalse :
  fixedOutputPairDifferencePaymentClayPromotion ≡ false
fixedOutputPairDifferencePaymentClayPromotionIsFalse = refl
