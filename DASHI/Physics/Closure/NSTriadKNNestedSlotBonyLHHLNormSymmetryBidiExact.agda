module DASHI.Physics.Closure.NSTriadKNNestedSlotBonyLHHLNormSymmetryBidiExact where

------------------------------------------------------------------------
-- LIVE R584 SLOT-TRANSFORMED LH <-> HL SYMMETRY
--
-- R585 proves that on a fixed nonzero inner output p, the literal fourSignInner
-- LH and HL folds are exactly equal.  R584 does not consume those raw inner
-- vectors directly: for a fixed outer incidence tau it applies the SAME linear
-- slot map
--
--   X |-> K(P_tau,Q_tau,X,u_qtau)
--
-- to every inner cell.  R309 proves that this map is additive in X.  Therefore
-- the R585 equality survives the actual R584 slot transform exactly.
--
-- Consequence: LH and HL class norms on the live nested-slot carrier are not
-- independent analytic coordinates.  No norm estimate, shell count, weight,
-- or spacetime inequality is used here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNComLiteralBonyOutputFibrePartitionRound63Exact as Bony
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNNestedProjectedForcingSlotExpansionRound309Exact as R309
import DASHI.Physics.Closure.NSTriadKNNestedComponentwiseInnerCommutatorRound572Exact as R572
import DASHI.Physics.Closure.NSTriadKNNestedSlotBonyClassNormBidiRound584Exact as R584
import DASHI.Physics.Closure.NSTriadKNFourSignInnerBonyLHHLNormSymmetryRound585Exact as R585
import DASHI.Physics.Closure.NSTriadKNLiteralFourSignBonyRoutingRound581Exact as R581

F : C3.RealField _
F = Rational.rationalRealField

module SlotSymmetry
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
  module Nested = R584.LiveNestedSlot584 W S L H system velocityTransverse
  module Swap = R585.LiveFourSignSwap585 system S L velocityTransverse

  P : Physical.PhysicalTriadIncidence → C3.Complex3 F
  P tau = R167.normalizedDirection E S (Physical.p tau)

  Q : Physical.PhysicalTriadIncidence → C3.Complex3 F
  Q tau = R167.normalizedDirection E S (Physical.q tau)

  uq : Physical.PhysicalTriadIncidence → C3.Complex3 F
  uq tau = Audit.velocity system (Physical.q tau)

  slot :
    Physical.PhysicalTriadIncidence →
    C3.Complex3 F → C3.Complex3 F
  slot tau value = R145.slotKernel (P tau) (Q tau) value (uq tau)

  slotZero :
    (tau : Physical.PhysicalTriadIncidence) →
    slot tau (C3.complex3Zero F) ≡ C3.complex3Zero F
  slotZero tau =
    R309.slotKernelFoldFirstAmplitude (P tau) (Q tau) (uq tau) []

  lowHighPointwiseCommutes :
    (tau innerTau : Physical.PhysicalTriadIncidence) →
    R581.lowHighCell581 (Nested.nestedSlotCell584 tau) innerTau
    ≡ slot tau (R581.lowHighCell581 Inner.fourSignInner innerTau)
  lowHighPointwiseCommutes tau innerTau with Bony.bonyTag innerTau
  ... | Bony.lhTag = refl
  ... | Bony.hlTag = sym (slotZero tau)
  ... | Bony.hhToLowTag = sym (slotZero tau)
  ... | Bony.comparableTag = sym (slotZero tau)

  highLowPointwiseCommutes :
    (tau innerTau : Physical.PhysicalTriadIncidence) →
    R581.highLowCell581 (Nested.nestedSlotCell584 tau) innerTau
    ≡ slot tau (R581.highLowCell581 Inner.fourSignInner innerTau)
  highLowPointwiseCommutes tau innerTau with Bony.bonyTag innerTau
  ... | Bony.lhTag = sym (slotZero tau)
  ... | Bony.hlTag = refl
  ... | Bony.hhToLowTag = sym (slotZero tau)
  ... | Bony.comparableTag = sym (slotZero tau)

  lowHighFoldCommutes :
    (tau : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector (R581.lowHighCell581 (Nested.nestedSlotCell584 tau)) items
    ≡ slot tau
        (R224.foldVector (R581.lowHighCell581 Inner.fourSignInner) items)
  lowHighFoldCommutes tau [] = sym (slotZero tau)
  lowHighFoldCommutes tau (innerTau ∷ rest) =
    let
      rawHead = R581.lowHighCell581 Inner.fourSignInner innerTau
      rawTail = R224.foldVector
        (R581.lowHighCell581 Inner.fourSignInner) rest
    in
    trans
      (cong₂ C3.complex3Add
        (lowHighPointwiseCommutes tau innerTau)
        (lowHighFoldCommutes tau rest))
      (sym (R309.slotKernelAdditiveFirstAmplitude
        (P tau) (Q tau) rawHead rawTail (uq tau)))

  highLowFoldCommutes :
    (tau : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector (R581.highLowCell581 (Nested.nestedSlotCell584 tau)) items
    ≡ slot tau
        (R224.foldVector (R581.highLowCell581 Inner.fourSignInner) items)
  highLowFoldCommutes tau [] = sym (slotZero tau)
  highLowFoldCommutes tau (innerTau ∷ rest) =
    let
      rawHead = R581.highLowCell581 Inner.fourSignInner innerTau
      rawTail = R224.foldVector
        (R581.highLowCell581 Inner.fourSignInner) rest
    in
    trans
      (cong₂ C3.complex3Add
        (highLowPointwiseCommutes tau innerTau)
        (highLowFoldCommutes tau rest))
      (sym (R309.slotKernelAdditiveFirstAmplitude
        (P tau) (Q tau) rawHead rawTail (uq tau)))

  nestedSlotLowHighEqualsHighLow :
    (tau : Physical.PhysicalTriadIncidence) →
    Z3.NonZeroMode (Physical.p tau) →
    let items = Output.physicalOutputFiber
          (Audit.cutoff system) (Physical.p tau)
    in
    R224.foldVector (R581.lowHighCell581 (Nested.nestedSlotCell584 tau)) items
    ≡ R224.foldVector (R581.highLowCell581 (Nested.nestedSlotCell584 tau)) items
  nestedSlotLowHighEqualsHighLow tau pNonzero =
    let
      items = Output.physicalOutputFiber
        (Audit.cutoff system) (Physical.p tau)
      rawEq = Swap.fixedOutputLowHighFoldEqualsHighLowFold585
        (Physical.p tau) pNonzero
    in
    trans
      (lowHighFoldCommutes tau items)
      (trans
        (cong (slot tau) rawEq)
        (sym (highLowFoldCommutes tau items)))

  nestedSlotLowHighNormEqualsHighLowNorm :
    (tau : Physical.PhysicalTriadIncidence) →
    Z3.NonZeroMode (Physical.p tau) →
    let items = Output.physicalOutputFiber
          (Audit.cutoff system) (Physical.p tau)
    in
    L2.complex3NormSquared
      (R224.foldVector (R581.lowHighCell581 (Nested.nestedSlotCell584 tau)) items)
    ≡
    L2.complex3NormSquared
      (R224.foldVector (R581.highLowCell581 (Nested.nestedSlotCell584 tau)) items)
  nestedSlotLowHighNormEqualsHighLowNorm tau pNonzero =
    cong L2.complex3NormSquared
      (nestedSlotLowHighEqualsHighLow tau pNonzero)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

slotTransformedLHHLExactlyEqual : Bool
slotTransformedLHHLExactlyEqual = true

slotTransformedLHHLRequireIndependentAnalyticBounds : Bool
slotTransformedLHHLRequireIndependentAnalyticBounds = false

newEstimateIntroduced : Bool
newEstimateIntroduced = false

clayPromotion : Bool
clayPromotion = false
