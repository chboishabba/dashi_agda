module DASHI.Physics.Closure.NSTriadKNFourSignInnerBonyLHHLNormSymmetryRound585Exact where

------------------------------------------------------------------------
-- ROUND585 / EXACT LH <-> HL SYMMETRY FOR THE LIVE FOUR-SIGN INNER FIBRE
--
-- The fourSignInner cell in R572 is pointwise equal, on a nonzero fixed-output
-- fibre, to R310.pairedInnerVector.  That paired vector is invariant under
-- physical p/q swap because it is literally term(tau)+term(swap tau).
-- R130 simultaneously proves that Bony tags exchange LH <-> HL under the same
-- swap, while R224 proves swap is a permutation of the literal output fibre.
--
-- Therefore the complete zero-masked LH and HL folds of the LIVE fourSignInner
-- carrier are exactly equal.  They are not independent analytic leaves.
-- No norm estimate, cardinality argument, or division by two is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNComLiteralBonyOutputFibrePartitionRound63Exact as Bony
import DASHI.Physics.Closure.NSTriadKNPhysicalBonyTagSwapRound130Exact as R130
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNNestedInnerSwapCommutatorRound310Exact as R310
import DASHI.Physics.Closure.NSTriadKNNestedComponentwiseInnerCommutatorRound572Exact as R572
import DASHI.Physics.Closure.NSTriadKNLiteralFourSignBonyRoutingRound581Exact as R581
import DASHI.Physics.Closure.NSTriadKNDirectBonyClassNormCompilerRound583Exact as R583
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = R583.F

module LiveFourSignSwap585
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module Inner = R572.ComponentwiseNested system S L velocityTransverse

  pairedInnerSwapInvariant585 :
    (tau : Physical.PhysicalTriadIncidence) →
    R310.pairedInnerVector system (Symmetry.swapTriad tau)
    ≡ R310.pairedInnerVector system tau
  pairedInnerSwapInvariant585 tau =
    trans
      (cong₂ C3.complex3Add
        refl
        (cong (Audit.projectedOrderedTerm system)
          (R38.swapTriadInvolutiveExact tau)))
      (Algebra.complex3AddCommutative
        (Audit.projectedOrderedTerm system (Symmetry.swapTriad tau))
        (Audit.projectedOrderedTerm system tau))

  fourSignInnerSwapInvariant585 :
    (output : Z3.FourierMode) →
    Z3.NonZeroMode output →
    (tau : Physical.PhysicalTriadIncidence) →
    tau Cube.∈ Output.physicalOutputFiber (Audit.cutoff system) output →
    Inner.fourSignInner (Symmetry.swapTriad tau)
    ≡ Inner.fourSignInner tau
  fourSignInnerSwapInvariant585 output outputNonzero tau member =
    trans
      (sym
        (Inner.pairedInnerPointwise output outputNonzero
          (Symmetry.swapTriad tau)
          (R224.swapOutputFibreMemberCube member)))
      (trans
        (pairedInnerSwapInvariant585 tau)
        (Inner.pairedInnerPointwise output outputNonzero tau member))

  lowHighAfterSwapIsHighLow585 :
    (output : Z3.FourierMode) →
    Z3.NonZeroMode output →
    (tau : Physical.PhysicalTriadIncidence) →
    tau Cube.∈ Output.physicalOutputFiber (Audit.cutoff system) output →
    R581.lowHighCell581 Inner.fourSignInner (Symmetry.swapTriad tau)
    ≡ R581.highLowCell581 Inner.fourSignInner tau
  lowHighAfterSwapIsHighLow585 output outputNonzero tau member
    with Bony.bonyTag tau | R130.bonyTagSwapEquivariant tau
  ... | Bony.lhTag | tagEq rewrite tagEq = refl
  ... | Bony.hlTag | tagEq rewrite tagEq =
    fourSignInnerSwapInvariant585 output outputNonzero tau member
  ... | Bony.hhToLowTag | tagEq rewrite tagEq = refl
  ... | Bony.comparableTag | tagEq rewrite tagEq = refl

  foldPointwise585 :
    (output : Z3.FourierMode) →
    Z3.NonZeroMode output →
    (items : List Physical.PhysicalTriadIncidence) →
    ((tau : Physical.PhysicalTriadIncidence) →
      tau Cube.∈ items →
      tau Cube.∈ Output.physicalOutputFiber (Audit.cutoff system) output) →
    R224.foldVector
      (λ tau → R581.lowHighCell581 Inner.fourSignInner
        (Symmetry.swapTriad tau)) items
    ≡ R224.foldVector
        (R581.highLowCell581 Inner.fourSignInner) items
  foldPointwise585 output outputNonzero [] included = refl
  foldPointwise585 output outputNonzero (tau ∷ rest) included =
    cong₂ C3.complex3Add
      (lowHighAfterSwapIsHighLow585 output outputNonzero tau
        (included tau (Cube.here refl)))
      (foldPointwise585 output outputNonzero rest
        (λ beta member → included beta (Cube.there member)))

  fixedOutputLowHighFoldEqualsHighLowFold585 :
    (output : Z3.FourierMode) →
    Z3.NonZeroMode output →
    R224.foldVector (R581.lowHighCell581 Inner.fourSignInner)
      (Output.physicalOutputFiber (Audit.cutoff system) output)
    ≡ R224.foldVector (R581.highLowCell581 Inner.fourSignInner)
      (Output.physicalOutputFiber (Audit.cutoff system) output)
  fixedOutputLowHighFoldEqualsHighLowFold585 output outputNonzero =
    let
      items = Output.physicalOutputFiber (Audit.cutoff system) output
      lh = R581.lowHighCell581 Inner.fourSignInner
    in
    trans
      (sym (R224.foldPermutationInvariant lh
        (R224.swapOutputFibrePermutation (Audit.cutoff system) output)))
      (trans
        (R224.foldMap lh Symmetry.swapTriad items)
        (foldPointwise585 output outputNonzero items
          (λ tau member → member)))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round585LiveFourSignInnerSwapInvariantOnFixedNonzeroOutput : Bool
round585LiveFourSignInnerSwapInvariantOnFixedNonzeroOutput = true

round585LowHighHighLowFoldsExactlyEqual : Bool
round585LowHighHighLowFoldsExactlyEqual = true

round585LHHLRequireIndependentNormTheorems : Bool
round585LHHLRequireIndependentNormTheorems = false

round585AnyThreeClassNormBudgetConstructed : Bool
round585AnyThreeClassNormBudgetConstructed = false

round585CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round585CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round585ClayPromotion : Bool
round585ClayPromotion = false

round585LowHighHighLowFoldsExactlyEqualIsTrue :
  round585LowHighHighLowFoldsExactlyEqual ≡ true
round585LowHighHighLowFoldsExactlyEqualIsTrue = refl

round585LHHLRequireIndependentNormTheoremsIsFalse :
  round585LHHLRequireIndependentNormTheorems ≡ false
round585LHHLRequireIndependentNormTheoremsIsFalse = refl

round585ClayPromotionIsFalse : round585ClayPromotion ≡ false
round585ClayPromotionIsFalse = refl
