module DASHI.Physics.Closure.NSTriadKNFourSignBonyClassGramCompilerRound580Exact where

------------------------------------------------------------------------
-- ROUND580 / FOUR-SIGN INNER FIBRE -> BONY-CLASS QUANTITATIVE GRAM COMPILER
--
-- R579 localises the unresolved inner aggregation to the signed Gram residual
-- of the literal fourSignInner convolution on physicalOutputFiber N p.
--
-- The repository already owns the exact four-way physical Bony partition
--   LH, HL, HH->low, CC,
-- and R576 owns the fixed four-vector inequality
--   ||A+B+C+D||^2 <= 4 (||A||^2+||B||^2+||C||^2+||D||^2).
--
-- Therefore the next least-privilege consumer is NOT one global absolute-value
-- estimate.  It is four quantitative within-class Gram payments plus one exact
-- finite routing equality.  Positive covariance is allowed; each class merely
-- supplies an upper residual.
--
-- This file proves that those receipts are sufficient.  It deliberately does
-- not manufacture the routing equality or any classwise analytic residual.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNFourHelicityVectorRecombinationRound576Exact as R576
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

record FourBonyClassCells580 : Set where
  constructor four-bony-class-cells-580
  field
    lowHigh580 highLow580 highHighToLow580 comparable580 :
      List (C3.Complex3 F)

open FourBonyClassCells580 public

lowHighSum580 highLowSum580 highHighToLowSum580 comparableSum580 :
  FourBonyClassCells580 → C3.Complex3 F
lowHighSum580 cells = R180.sumCells (lowHigh580 cells)
highLowSum580 cells = R180.sumCells (highLow580 cells)
highHighToLowSum580 cells = R180.sumCells (highHighToLow580 cells)
comparableSum580 cells = R180.sumCells (comparable580 cells)

routedFourClassVector580 : FourBonyClassCells580 → C3.Complex3 F
routedFourClassVector580 cells =
  R576.fourVectorTotal
    (lowHighSum580 cells)
    (highLowSum580 cells)
    (highHighToLowSum580 cells)
    (comparableSum580 cells)

record FourBonyClassGramPayment580 (cells : FourBonyClassCells580) : Set where
  constructor four-bony-class-gram-payment-580
  field
    lowHighResidual580 highLowResidual580
      highHighToLowResidual580 comparableResidual580 : ℚ

    lowHighDebtUpper580 :
      R180.gramDebt (lowHigh580 cells) ≤ lowHighResidual580
    highLowDebtUpper580 :
      R180.gramDebt (highLow580 cells) ≤ highLowResidual580
    highHighToLowDebtUpper580 :
      R180.gramDebt (highHighToLow580 cells) ≤ highHighToLowResidual580
    comparableDebtUpper580 :
      R180.gramDebt (comparable580 cells) ≤ comparableResidual580

open FourBonyClassGramPayment580 public

classMassPlusResidual580 : List (C3.Complex3 F) → ℚ → ℚ
classMassPlusResidual580 cells residual = R180.cellMassSum cells + residual

classBound580 :
  (cells : List (C3.Complex3 F)) →
  (residual : ℚ) →
  R180.gramDebt cells ≤ residual →
  L2.complex3NormSquared (R180.sumCells cells)
  ≤ classMassPlusResidual580 cells residual
classBound580 cells residual debtUpper =
  subst
    (λ lhs → lhs ≤ R180.cellMassSum cells + residual)
    (R180.finiteFibreGramLedger cells)
    (ℚP.+-monoʳ-≤ (R180.cellMassSum cells) debtUpper)

fourClassScalarEnvelope580 :
  (cells : FourBonyClassCells580) →
  FourBonyClassGramPayment580 cells → ℚ
fourClassScalarEnvelope580 cells payment =
    classMassPlusResidual580 (lowHigh580 cells) (lowHighResidual580 payment)
  + classMassPlusResidual580 (highLow580 cells) (highLowResidual580 payment)
  + classMassPlusResidual580 (highHighToLow580 cells) (highHighToLowResidual580 payment)
  + classMassPlusResidual580 (comparable580 cells) (comparableResidual580 payment)

fourClassPaymentsBoundRoutedVector580 :
  (cells : FourBonyClassCells580) →
  (payment : FourBonyClassGramPayment580 cells) →
  L2.complex3NormSquared (routedFourClassVector580 cells)
  ≤ R576.four * fourClassScalarEnvelope580 cells payment
fourClassPaymentsBoundRoutedVector580 cells payment =
  let
    lh = lowHighSum580 cells
    hl = highLowSum580 cells
    hh = highHighToLowSum580 cells
    cc = comparableSum580 cells

    fixedFour = R576.fourVectorSumNormSquaredBound lh hl hh cc

    classBounds :
      L2.complex3NormSquared lh
        + L2.complex3NormSquared hl
        + L2.complex3NormSquared hh
        + L2.complex3NormSquared cc
      ≤ fourClassScalarEnvelope580 cells payment
    classBounds =
      ℚP.+-mono-≤
        (ℚP.+-mono-≤
          (ℚP.+-mono-≤
            (classBound580 (lowHigh580 cells) (lowHighResidual580 payment)
              (lowHighDebtUpper580 payment))
            (classBound580 (highLow580 cells) (highLowResidual580 payment)
              (highLowDebtUpper580 payment)))
          (classBound580 (highHighToLow580 cells) (highHighToLowResidual580 payment)
            (highHighToLowDebtUpper580 payment)))
        (classBound580 (comparable580 cells) (comparableResidual580 payment)
          (comparableDebtUpper580 payment))

    scaled =
      let instance fourNNI = nonNegative R576.fourNN
      in ℚP.*-monoˡ-≤-nonNeg R576.four classBounds
  in
  ℚP.≤-trans fixedFour scaled

record LiteralToBonyRouting580
    (literalVector : C3.Complex3 F)
    (cells : FourBonyClassCells580) : Set where
  constructor literal-to-bony-routing-580
  field
    literalEqualsRouted580 : literalVector ≡ routedFourClassVector580 cells

open LiteralToBonyRouting580 public

literalBoundFromBonyPayments580 :
  (literalVector : C3.Complex3 F) →
  (cells : FourBonyClassCells580) →
  LiteralToBonyRouting580 literalVector cells →
  (payment : FourBonyClassGramPayment580 cells) →
  L2.complex3NormSquared literalVector
  ≤ R576.four * fourClassScalarEnvelope580 cells payment
literalBoundFromBonyPayments580 literalVector cells routing payment =
  subst
    (λ routed →
      L2.complex3NormSquared routed
      ≤ R576.four * fourClassScalarEnvelope580 cells payment)
    (sym (literalEqualsRouted580 routing))
    (fourClassPaymentsBoundRoutedVector580 cells payment)

------------------------------------------------------------------------
-- Status / frontier.
------------------------------------------------------------------------

round580FourClassQuantitativeGramCompilerClosed : Bool
round580FourClassQuantitativeGramCompilerClosed = true

round580RequiresClassGramNegativity : Bool
round580RequiresClassGramNegativity = false

round580FixedCrossClassCostDependsOnCutoff : Bool
round580FixedCrossClassCostDependsOnCutoff = false

round580LiteralBonyRoutingReceiptConstructed : Bool
round580LiteralBonyRoutingReceiptConstructed = false

round580LowHighGramResidualPaid : Bool
round580LowHighGramResidualPaid = false

round580HighLowGramResidualPaid : Bool
round580HighLowGramResidualPaid = false

round580HighHighToLowGramResidualPaid : Bool
round580HighHighToLowGramResidualPaid = false

round580ComparableGramResidualPaid : Bool
round580ComparableGramResidualPaid = false

round580OuterSpectatorWeightedSpacetimeBoundClosed : Bool
round580OuterSpectatorWeightedSpacetimeBoundClosed = false

round580CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round580CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round580ClayPromotion : Bool
round580ClayPromotion = false

round580FourClassQuantitativeGramCompilerClosedIsTrue :
  round580FourClassQuantitativeGramCompilerClosed ≡ true
round580FourClassQuantitativeGramCompilerClosedIsTrue = refl

round580ClayPromotionIsFalse : round580ClayPromotion ≡ false
round580ClayPromotionIsFalse = refl
