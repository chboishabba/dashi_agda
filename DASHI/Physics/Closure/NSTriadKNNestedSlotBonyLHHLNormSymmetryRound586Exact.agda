module DASHI.Physics.Closure.NSTriadKNNestedSlotBonyLHHLNormSymmetryRound586Exact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNComLiteralBonyOutputFibrePartitionRound63Exact as Bony
import DASHI.Physics.Closure.NSTriadKNPhysicalBonyTagSwapRound130Exact as R130
import DASHI.Physics.Closure.NSTriadKNLiteralFourSignBonyRoutingRound581Exact as R581
import DASHI.Physics.Closure.NSTriadKNDirectBonyClassNormCompilerRound583Exact as R583
import DASHI.Physics.Closure.NSTriadKNNestedSlotBonyClassNormBidiRound584Exact as R584
import DASHI.Physics.Closure.NSTriadKNFourSignInnerBonyLHHLNormSymmetryRound585Exact as R585
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = R583.F

module LiveNestedSlotSwap586
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
  module InnerSwap = R585.LiveFourSignSwap585 system S L velocityTransverse

  nestedSlotCellSwapInvariant586 :
    (outer : Physical.PhysicalTriadIncidence) →
    Z3.NonZeroMode (Physical.p outer) →
    (inner : Physical.PhysicalTriadIncidence) →
    inner Cube.∈ Output.physicalOutputFiber
      (Audit.cutoff system) (Physical.p outer) →
    Slot.nestedSlotCell584 outer (Symmetry.swapTriad inner)
    ≡ Slot.nestedSlotCell584 outer inner
  nestedSlotCellSwapInvariant586 outer pNonzero inner member =
    cong
      (λ forcing →
        R145.slotKernel
          (R167.normalizedDirection E S (Physical.p outer))
          (R167.normalizedDirection E S (Physical.q outer))
          forcing
          (Audit.velocity system (Physical.q outer)))
      (InnerSwap.fourSignInnerSwapInvariant585
        (Physical.p outer) pNonzero inner member)

  lowHighAfterSwapIsHighLow586 :
    (outer : Physical.PhysicalTriadIncidence) →
    Z3.NonZeroMode (Physical.p outer) →
    (inner : Physical.PhysicalTriadIncidence) →
    inner Cube.∈ Output.physicalOutputFiber
      (Audit.cutoff system) (Physical.p outer) →
    R581.lowHighCell581 (Slot.nestedSlotCell584 outer)
      (Symmetry.swapTriad inner)
    ≡ R581.highLowCell581 (Slot.nestedSlotCell584 outer) inner
  lowHighAfterSwapIsHighLow586 outer pNonzero inner member
    with Bony.bonyTag inner | R130.bonyTagSwapEquivariant inner
  ... | Bony.lhTag | tagEq rewrite tagEq = refl
  ... | Bony.hlTag | tagEq rewrite tagEq =
    nestedSlotCellSwapInvariant586 outer pNonzero inner member
  ... | Bony.hhToLowTag | tagEq rewrite tagEq = refl
  ... | Bony.comparableTag | tagEq rewrite tagEq = refl

  foldPointwise586 :
    (outer : Physical.PhysicalTriadIncidence) →
    Z3.NonZeroMode (Physical.p outer) →
    (items : List Physical.PhysicalTriadIncidence) →
    ((inner : Physical.PhysicalTriadIncidence) →
      inner Cube.∈ items →
      inner Cube.∈ Output.physicalOutputFiber
        (Audit.cutoff system) (Physical.p outer)) →
    R224.foldVector
      (λ inner → R581.lowHighCell581 (Slot.nestedSlotCell584 outer)
        (Symmetry.swapTriad inner)) items
    ≡ R224.foldVector
        (R581.highLowCell581 (Slot.nestedSlotCell584 outer)) items
  foldPointwise586 outer pNonzero [] included = refl
  foldPointwise586 outer pNonzero (inner ∷ rest) included =
    cong₂ C3.complex3Add
      (lowHighAfterSwapIsHighLow586 outer pNonzero inner
        (included inner (Cube.here refl)))
      (foldPointwise586 outer pNonzero rest
        (λ beta member → included beta (Cube.there member)))

  nestedSlotLowHighFoldEqualsHighLowFold586 :
    (outer : Physical.PhysicalTriadIncidence) →
    Z3.NonZeroMode (Physical.p outer) →
    R224.foldVector (R581.lowHighCell581 (Slot.nestedSlotCell584 outer))
      (Output.physicalOutputFiber
        (Audit.cutoff system) (Physical.p outer))
    ≡ R224.foldVector (R581.highLowCell581 (Slot.nestedSlotCell584 outer))
      (Output.physicalOutputFiber
        (Audit.cutoff system) (Physical.p outer))
  nestedSlotLowHighFoldEqualsHighLowFold586 outer pNonzero =
    let
      items = Output.physicalOutputFiber
        (Audit.cutoff system) (Physical.p outer)
      lh = R581.lowHighCell581 (Slot.nestedSlotCell584 outer)
    in
    trans
      (sym (R224.foldPermutationInvariant lh
        (R224.swapOutputFibrePermutation
          (Audit.cutoff system) (Physical.p outer))))
      (trans
        (R224.foldMap lh Symmetry.swapTriad items)
        (foldPointwise586 outer pNonzero items
          (λ inner member → member)))

round586LiveNestedSlotLHHLFoldsExactlyEqual : Bool
round586LiveNestedSlotLHHLFoldsExactlyEqual = true

round586NonzeroOuterPRequiresTwoIndependentFarLowNormBudgets : Bool
round586NonzeroOuterPRequiresTwoIndependentFarLowNormBudgets = false

round586ZeroOuterPHandledByR573SeparateZeroBranch : Bool
round586ZeroOuterPHandledByR573SeparateZeroBranch = true

round586ThreeLiveClassNormTheoremsConstructed : Bool
round586ThreeLiveClassNormTheoremsConstructed = false

round586CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round586CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round586ClayPromotion : Bool
round586ClayPromotion = false
