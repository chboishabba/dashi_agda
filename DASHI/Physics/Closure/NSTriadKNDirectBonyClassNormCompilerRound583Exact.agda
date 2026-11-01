module DASHI.Physics.Closure.NSTriadKNDirectBonyClassNormCompilerRound583Exact where

------------------------------------------------------------------------
-- ROUND583 / DIRECT CLASS-NORM COMPILER: BYPASS GRAM DEBT WHEN A STRONGER
-- CLASS NORM ESTIMATE IS ALREADY AVAILABLE
--
-- R582 showed that a class norm budget is sufficient to pay R580's Gram
-- residual.  But if the analytic producer already proves the stronger object
--
--   ||sum(class cells)||^2 <= B_class,
--
-- then routing through
--
--   norm bound -> Gram residual -> mass + residual -> routed norm
--
-- is unnecessary and weakens constants.  R581 already gives the exact literal
-- four-way routing, while R576 gives the fixed four-vector inequality.
-- Therefore the shortest consumer is simply
--
--   four class norm bounds -> literal fourSignInner fibre norm bound,
--
-- with universal factor 4 and no cutoff/fibre-cardinality factor.
--
-- This does NOT prove any class norm estimate.  It only removes Gram payment
-- as a mandatory intermediate representation when Schur/Young/operator
-- machinery already lands directly in a class norm ceiling.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFourHelicityVectorRecombinationRound576Exact as R576
import DASHI.Physics.Closure.NSTriadKNFourSignBonyClassGramCompilerRound580Exact as R580
import DASHI.Physics.Closure.NSTriadKNLiteralFourSignBonyRoutingRound581Exact as R581
import DASHI.Physics.Closure.NSTriadKNClassNormBudgetToBonyGramPaymentRound582Exact as R582
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

fourClassNormEnvelope583 :
  (cells : R580.FourBonyClassCells580) →
  R582.FourBonyClassNormBudgets582 cells → ℚ
fourClassNormEnvelope583 cells budgets =
    R582.classNormCeiling582 (R582.lowHighNormBudget582 budgets)
  + R582.classNormCeiling582 (R582.highLowNormBudget582 budgets)
  + R582.classNormCeiling582 (R582.highHighToLowNormBudget582 budgets)
  + R582.classNormCeiling582 (R582.comparableNormBudget582 budgets)

fourClassNormBudgetsBoundRouted583 :
  (cells : R580.FourBonyClassCells580) →
  (budgets : R582.FourBonyClassNormBudgets582 cells) →
  L2.complex3NormSquared (R580.routedFourClassVector580 cells)
  ≤ R576.four * fourClassNormEnvelope583 cells budgets
fourClassNormBudgetsBoundRouted583 cells budgets =
  let
    lh = R580.lowHighSum580 cells
    hl = R580.highLowSum580 cells
    hh = R580.highHighToLowSum580 cells
    cc = R580.comparableSum580 cells

    fixedFour = R576.fourVectorSumNormSquaredBound lh hl hh cc

    classBounds :
      L2.complex3NormSquared lh
        + L2.complex3NormSquared hl
        + L2.complex3NormSquared hh
        + L2.complex3NormSquared cc
      ≤ fourClassNormEnvelope583 cells budgets
    classBounds =
      ℚP.+-mono-≤
        (ℚP.+-mono-≤
          (ℚP.+-mono-≤
            (R582.classSummedNormBound582 (R582.lowHighNormBudget582 budgets))
            (R582.classSummedNormBound582 (R582.highLowNormBudget582 budgets)))
          (R582.classSummedNormBound582 (R582.highHighToLowNormBudget582 budgets)))
        (R582.classSummedNormBound582 (R582.comparableNormBudget582 budgets))

    scaled =
      let instance fourNNI = nonNegative R576.fourNN
      in ℚP.*-monoˡ-≤-nonNeg R576.four classBounds
  in
  ℚP.≤-trans fixedFour scaled

literalBoundFromDirectClassNorms583 :
  (literalVector : C3.Complex3 F) →
  (cells : R580.FourBonyClassCells580) →
  R580.LiteralToBonyRouting580 literalVector cells →
  (budgets : R582.FourBonyClassNormBudgets582 cells) →
  L2.complex3NormSquared literalVector
  ≤ R576.four * fourClassNormEnvelope583 cells budgets
literalBoundFromDirectClassNorms583 literalVector cells routing budgets =
  subst
    (λ routed →
      L2.complex3NormSquared routed
      ≤ R576.four * fourClassNormEnvelope583 cells budgets)
    (sym (R580.literalEqualsRouted580 routing))
    (fourClassNormBudgetsBoundRouted583 cells budgets)

literalRoutedFourSignBound583 :
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  (budgets : R582.FourBonyClassNormBudgets582 (R581.bonyClassCells581 value items)) →
  L2.complex3NormSquared (R224.foldVector value items)
  ≤ R576.four *
      fourClassNormEnvelope583 (R581.bonyClassCells581 value items) budgets
literalRoutedFourSignBound583 value items budgets =
  literalBoundFromDirectClassNorms583
    (R224.foldVector value items)
    (R581.bonyClassCells581 value items)
    (R581.literalRouting581 value items)
    budgets

------------------------------------------------------------------------
-- Status / proof-search correction.
------------------------------------------------------------------------

round583DirectClassNormCompilerClosed : Bool
round583DirectClassNormCompilerClosed = true

round583GramResidualPaymentMandatoryForClassNormProducer : Bool
round583GramResidualPaymentMandatoryForClassNormProducer = false

round583CrossClassCostDependsOnCutoff : Bool
round583CrossClassCostDependsOnCutoff = false

round583AnyLiteralClassNormBudgetConstructed : Bool
round583AnyLiteralClassNormBudgetConstructed = false

round583OuterSpectatorWeightedSpacetimeBoundClosed : Bool
round583OuterSpectatorWeightedSpacetimeBoundClosed = false

round583CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round583CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round583ClayPromotion : Bool
round583ClayPromotion = false

round583DirectClassNormCompilerClosedIsTrue :
  round583DirectClassNormCompilerClosed ≡ true
round583DirectClassNormCompilerClosedIsTrue = refl

round583GramResidualPaymentMandatoryForClassNormProducerIsFalse :
  round583GramResidualPaymentMandatoryForClassNormProducer ≡ false
round583GramResidualPaymentMandatoryForClassNormProducerIsFalse = refl

round583ClayPromotionIsFalse : round583ClayPromotion ≡ false
round583ClayPromotionIsFalse = refl
