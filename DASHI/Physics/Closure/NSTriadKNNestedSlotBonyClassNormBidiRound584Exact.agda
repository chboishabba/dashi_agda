module DASHI.Physics.Closure.NSTriadKNNestedSlotBonyClassNormBidiRound584Exact where

------------------------------------------------------------------------
-- ROUND584 / BIDI THE DIRECT R583 CLASS-NORM COMPILER ONTO R573'S ACTUAL
-- NESTED OUTER SLOT
--
-- R583 is generic in the value carried by each physical inner incidence.  The
-- live R573 object is not merely fourSignInner itself; for a fixed outer cell
-- tau it is the literal inner fibre
--
--   innerTau |-> K(P_tau,Q_tau,fourSignInner(innerTau),u_qtau).
--
-- This round instantiates R581/R583 on exactly that value and exactly the
-- physicalOutputFiber N p_tau.  Thus the remaining class budgets are now on
-- the SAME slot-transformed cells consumed by the modern weighted commutator.
-- No substitution of the older raw-curl class carrier is made.
--
-- R580-R583 currently live on the exact rational C3 carrier, so this BIDI is
-- deliberately rational too; it does not pretend to be scalar-generic.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (_≤_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNNestedComponentwiseInnerCommutatorRound572Exact as R572
import DASHI.Physics.Closure.NSTriadKNWeightedNestedComponentwiseCommutatorRound573Exact as R573
import DASHI.Physics.Closure.NSTriadKNFourSignBonyClassGramCompilerRound580Exact as R580
import DASHI.Physics.Closure.NSTriadKNLiteralFourSignBonyRoutingRound581Exact as R581
import DASHI.Physics.Closure.NSTriadKNClassNormBudgetToBonyGramPaymentRound582Exact as R582
import DASHI.Physics.Closure.NSTriadKNDirectBonyClassNormCompilerRound583Exact as R583
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNFourHelicityVectorRecombinationRound576Exact as R576
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = R583.F

module LiveNestedSlot584
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

  module Inner = R572.ComponentwiseNested system S L velocityTransverse
  module Weighted = R573.WeightedNested W S L H system velocityTransverse

  nestedSlotCell584 :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence →
    C3.Complex3 F
  nestedSlotCell584 tau innerTau =
    R145.slotKernel
      (R167.normalizedDirection E S (Physical.p tau))
      (R167.normalizedDirection E S (Physical.q tau))
      (Inner.fourSignInner innerTau)
      (Audit.velocity system (Physical.q tau))

  nestedSlotCells584 :
    (tau : Physical.PhysicalTriadIncidence) →
    R580.FourBonyClassCells580
  nestedSlotCells584 tau =
    R581.bonyClassCells581
      (nestedSlotCell584 tau)
      (Output.physicalOutputFiber
        (Audit.cutoff system) (Physical.p tau))

  nestedSlotFoldIsLiteralFold584 :
    (tau : Physical.PhysicalTriadIncidence) →
    Weighted.nestedSlotFold tau
    ≡ R224.foldVector
        (nestedSlotCell584 tau)
        (Output.physicalOutputFiber
          (Audit.cutoff system) (Physical.p tau))
  nestedSlotFoldIsLiteralFold584 tau = refl

  record NestedSlotClassNormPayment584
      (tau : Physical.PhysicalTriadIncidence) : Set where
    constructor nested-slot-class-norm-payment-584
    field
      budgets584 :
        R582.FourBonyClassNormBudgets582 (nestedSlotCells584 tau)

  open NestedSlotClassNormPayment584 public

  nestedSlotFoldBelowClassNorms584 :
    (tau : Physical.PhysicalTriadIncidence) →
    (payment : NestedSlotClassNormPayment584 tau) →
    L2.complex3NormSquared (Weighted.nestedSlotFold tau)
    ≤ R576.four *
        R583.fourClassNormEnvelope583
          (nestedSlotCells584 tau) (budgets584 payment)
  nestedSlotFoldBelowClassNorms584 tau payment =
    R583.literalRoutedFourSignBound583
      (nestedSlotCell584 tau)
      (Output.physicalOutputFiber
        (Audit.cutoff system) (Physical.p tau))
      (budgets584 payment)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round584LiveR573NestedSlotBidiClosed : Bool
round584LiveR573NestedSlotBidiClosed = true

round584UsesOlderRawCurlClassAsSameObject : Bool
round584UsesOlderRawCurlClassAsSameObject = false

round584AnyLiveNestedSlotClassNormPaymentConstructed : Bool
round584AnyLiveNestedSlotClassNormPaymentConstructed = false

round584OuterWeightAndSpectatorSpacetimeClosed : Bool
round584OuterWeightAndSpectatorSpacetimeClosed = false

round584CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round584CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round584ClayPromotion : Bool
round584ClayPromotion = false

round584LiveR573NestedSlotBidiClosedIsTrue :
  round584LiveR573NestedSlotBidiClosed ≡ true
round584LiveR573NestedSlotBidiClosedIsTrue = refl

round584ClayPromotionIsFalse : round584ClayPromotion ≡ false
round584ClayPromotionIsFalse = refl
