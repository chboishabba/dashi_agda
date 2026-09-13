module DASHI.Physics.Closure.NSTriadKNR329R572FourSignSameSlotBidiExact where

------------------------------------------------------------------------
-- R329 SINGLE NESTED CELL <-> R572 FOUR-SIGN SINGLE-INNER PRESENTATION
--
-- R329 stores one inner incidence and one outer incidence.  R572 proves that,
-- on the literal physical inner output fibre, R310's paired inner vector is
-- exactly the four-sign multiplier-difference vector.  This owner transports
-- that pointwise equality through the SAME R145 outer slot and R294 weight.
--
-- It deliberately does NOT identify one R329 cell with R573's complete outer
-- cell: R573 has already folded the whole inner fibre.  The remaining bridge is
-- only finite inner-fibre aggregation, which is structural and already owned by
-- R572/R309/R435.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNStrongLowLiteralNestedKernelRound329Exact as R329
import DASHI.Physics.Closure.NSTriadKNNestedComponentwiseInnerCommutatorRound572Exact as R572

F : C3.RealField _
F = Rational.rationalRealField

module SameSlot
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (W : R294.SwapInvariantCellWeight F)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module New = R572.ComponentwiseNested system S L velocityTransverse

  fourSignOuterSlot :
    (C : R329.StrongLowLiteralNestedCell E I O system S L H W) →
    C3.Complex3 F
  fourSignOuterSlot C =
    R145.slotKernel
      (R167.normalizedDirection E S (Physical.p (R329.outer C)))
      (R167.normalizedDirection E S (Physical.q (R329.outer C)))
      (New.fourSignInner (R329.inner C))
      (Audit.velocity system (Physical.q (R329.outer C)))

  weightedFourSignOuterSlot :
    (C : R329.StrongLowLiteralNestedCell E I O system S L H W) →
    C3.Complex3 F
  weightedFourSignOuterSlot C =
    C3.complex3Scale
      (R294.weight W (R329.outer C))
      (fourSignOuterSlot C)

  r329InnerPairedForcingIsFourSignInner :
    (C : R329.StrongLowLiteralNestedCell E I O system S L H W) →
    (pNonzero : Z3.NonZeroMode (Physical.p (R329.outer C))) →
    R329.inner C Cube.∈
      Output.physicalOutputFiber
        (Audit.cutoff system) (Physical.p (R329.outer C)) →
    R329.innerPairedForcing E I O system S L H W C
    ≡ New.fourSignInner (R329.inner C)
  r329InnerPairedForcingIsFourSignInner C pNonzero member =
    New.pairedInnerPointwise
      (Physical.p (R329.outer C)) pNonzero (R329.inner C) member

  r329OuterSlotIsFourSignOuterSlot :
    (C : R329.StrongLowLiteralNestedCell E I O system S L H W) →
    (pNonzero : Z3.NonZeroMode (Physical.p (R329.outer C))) →
    (member : R329.inner C Cube.∈
      Output.physicalOutputFiber
        (Audit.cutoff system) (Physical.p (R329.outer C))) →
    R329.literalNestedOuterSlot E I O system S L H W C
    ≡ fourSignOuterSlot C
  r329OuterSlotIsFourSignOuterSlot C pNonzero member =
    cong
      (λ forcing →
        R145.slotKernel
          (R167.normalizedDirection E S (Physical.p (R329.outer C)))
          (R167.normalizedDirection E S (Physical.q (R329.outer C)))
          forcing
          (Audit.velocity system (Physical.q (R329.outer C))))
      (r329InnerPairedForcingIsFourSignInner C pNonzero member)

  r329WeightedCellIsFourSignWeightedCell :
    (C : R329.StrongLowLiteralNestedCell E I O system S L H W) →
    (pNonzero : Z3.NonZeroMode (Physical.p (R329.outer C))) →
    (member : R329.inner C Cube.∈
      Output.physicalOutputFiber
        (Audit.cutoff system) (Physical.p (R329.outer C))) →
    R329.literalWeightedNestedCell E I O system S L H W C
    ≡ weightedFourSignOuterSlot C
  r329WeightedCellIsFourSignWeightedCell C pNonzero member =
    cong
      (C3.complex3Scale (R294.weight W (R329.outer C)))
      (r329OuterSlotIsFourSignOuterSlot C pNonzero member)

------------------------------------------------------------------------
-- Status / same-object boundary.
------------------------------------------------------------------------

r329SingleInnerCellToR572FourSignPresentationClosed : Bool
r329SingleInnerCellToR572FourSignPresentationClosed = true

r329SingleCellIdentifiedWithCompleteR573OuterFold : Bool
r329SingleCellIdentifiedWithCompleteR573OuterFold = false

remainingR329ToR573BridgeIsFiniteInnerAggregation : Bool
remainingR329ToR573BridgeIsFiniteInnerAggregation = true

newNormOrAbsoluteValueIntroduced : Bool
newNormOrAbsoluteValueIntroduced = false

newAnalyticEstimateIntroduced : Bool
newAnalyticEstimateIntroduced = false

clayPromotion : Bool
clayPromotion = false

r329SingleInnerCellToR572FourSignPresentationClosedIsTrue :
  r329SingleInnerCellToR572FourSignPresentationClosed ≡ true
r329SingleInnerCellToR572FourSignPresentationClosedIsTrue = refl

remainingR329ToR573BridgeIsFiniteInnerAggregationIsTrue :
  remainingR329ToR573BridgeIsFiniteInnerAggregation ≡ true
remainingR329ToR573BridgeIsFiniteInnerAggregationIsTrue = refl
