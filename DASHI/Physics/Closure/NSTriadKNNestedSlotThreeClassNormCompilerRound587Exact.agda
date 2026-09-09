module DASHI.Physics.Closure.NSTriadKNNestedSlotThreeClassNormCompilerRound587Exact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNFourSignBonyClassGramCompilerRound580Exact as R580
import DASHI.Physics.Closure.NSTriadKNLiteralFourSignBonyRoutingRound581Exact as R581
import DASHI.Physics.Closure.NSTriadKNClassNormBudgetToBonyGramPaymentRound582Exact as R582
import DASHI.Physics.Closure.NSTriadKNDirectBonyClassNormCompilerRound583Exact as R583
import DASHI.Physics.Closure.NSTriadKNNestedSlotBonyClassNormBidiRound584Exact as R584
import DASHI.Physics.Closure.NSTriadKNNestedSlotBonyLHHLNormSymmetryRound586Exact as R586
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNFourHelicityVectorRecombinationRound576Exact as R576
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = R583.F

module LiveThreeClass587
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module Slot = R584.LiveNestedSlot584 W S L H system velocityTransverse
  module Swap = R586.LiveNestedSlotSwap586 W S L H system velocityTransverse

  cells587 : Physical.PhysicalTriadIncidence → R580.FourBonyClassCells580
  cells587 = Slot.nestedSlotCells584

  lowHighSumEqualsHighLowSum587 :
    (outer : Physical.PhysicalTriadIncidence) →
    (pNonzero : Z3.NonZeroMode (Physical.p outer)) →
    R180.sumCells (R580.lowHigh580 (cells587 outer))
    ≡ R180.sumCells (R580.highLow580 (cells587 outer))
  lowHighSumEqualsHighLowSum587 outer pNonzero =
    let
      items = Output.physicalOutputFiber
        (Audit.cutoff system) (Physical.p outer)
      lh = R581.lowHighCell581 (Slot.nestedSlotCell584 outer)
      hl = R581.highLowCell581 (Slot.nestedSlotCell584 outer)
    in
    trans
      (R581.sumCellsMapAsFold581 lh items)
      (trans
        (Swap.nestedSlotLowHighFoldEqualsHighLowFold586 outer pNonzero)
        (sym (R581.sumCellsMapAsFold581 hl items)))

  record ThreeClassNormBudgets587
      (outer : Physical.PhysicalTriadIncidence) : Set where
    constructor three-class-norm-budgets-587
    field
      farLowNormBudget587 :
        R582.ClassNormBudget582 (R580.lowHigh580 (cells587 outer))
      highHighToLowNormBudget587 :
        R582.ClassNormBudget582 (R580.highHighToLow580 (cells587 outer))
      comparableNormBudget587 :
        R582.ClassNormBudget582 (R580.comparable580 (cells587 outer))

  open ThreeClassNormBudgets587 public

  highLowBudgetFromFarLow587 :
    (outer : Physical.PhysicalTriadIncidence) →
    (pNonzero : Z3.NonZeroMode (Physical.p outer)) →
    (budgets : ThreeClassNormBudgets587 outer) →
    R582.ClassNormBudget582 (R580.highLow580 (cells587 outer))
  highLowBudgetFromFarLow587 outer pNonzero budgets =
    R582.class-norm-budget-582 ceiling transported
    where
    source = farLowNormBudget587 budgets
    ceiling = R582.classNormCeiling582 source

    sumEq = lowHighSumEqualsHighLowSum587 outer pNonzero

    normEq :
      L2.complex3NormSquared
        (R180.sumCells (R580.lowHigh580 (cells587 outer)))
      ≡ L2.complex3NormSquared
        (R180.sumCells (R580.highLow580 (cells587 outer)))
    normEq = cong L2.complex3NormSquared sumEq

    transported :
      L2.complex3NormSquared
        (R180.sumCells (R580.highLow580 (cells587 outer)))
      ≤ ceiling
    transported =
      subst
        (λ lower → lower ≤ ceiling)
        normEq
        (R582.classSummedNormBound582 source)

  fourBudgetsFromThree587 :
    (outer : Physical.PhysicalTriadIncidence) →
    (pNonzero : Z3.NonZeroMode (Physical.p outer)) →
    ThreeClassNormBudgets587 outer →
    R582.FourBonyClassNormBudgets582 (cells587 outer)
  fourBudgetsFromThree587 outer pNonzero budgets =
    R582.four-bony-class-norm-budgets-582
      (farLowNormBudget587 budgets)
      (highLowBudgetFromFarLow587 outer pNonzero budgets)
      (highHighToLowNormBudget587 budgets)
      (comparableNormBudget587 budgets)

  nestedSlotFoldBelowThreeClassNorms587 :
    (outer : Physical.PhysicalTriadIncidence) →
    (pNonzero : Z3.NonZeroMode (Physical.p outer)) →
    (budgets : ThreeClassNormBudgets587 outer) →
    L2.complex3NormSquared
      (R224.foldVector
        (Slot.nestedSlotCell584 outer)
        (Output.physicalOutputFiber
          (Audit.cutoff system) (Physical.p outer)))
    ≤ R576.four *
        R583.fourClassNormEnvelope583
          (cells587 outer)
          (fourBudgetsFromThree587 outer pNonzero budgets)
  nestedSlotFoldBelowThreeClassNorms587 outer pNonzero budgets =
    R583.literalRoutedFourSignBound583
      (Slot.nestedSlotCell584 outer)
      (Output.physicalOutputFiber
        (Audit.cutoff system) (Physical.p outer))
      (fourBudgetsFromThree587 outer pNonzero budgets)

round587PreferredLiveInnerClassCountIsThree : Bool
round587PreferredLiveInnerClassCountIsThree = true

round587FourIndependentClassNormTheoremsRequired : Bool
round587FourIndependentClassNormTheoremsRequired = false

round587ThreeIndependentClassNormCoordinatesRemain : Bool
round587ThreeIndependentClassNormCoordinatesRemain = true

round587AnyOfThreeClassNormCoordinatesPaid : Bool
round587AnyOfThreeClassNormCoordinatesPaid = false

round587OuterWeightSpectatorSpacetimeClosed : Bool
round587OuterWeightSpectatorSpacetimeClosed = false

round587CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round587CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round587ClayPromotion : Bool
round587ClayPromotion = false
