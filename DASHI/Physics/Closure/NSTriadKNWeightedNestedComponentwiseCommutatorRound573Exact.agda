module DASHI.Physics.Closure.NSTriadKNWeightedNestedComponentwiseCommutatorRound573Exact where

------------------------------------------------------------------------
-- ROUND573 / R438 WEIGHTED OUTER COMMUTATOR -> NESTED FOUR-SIGN INNER FORM
--
-- R438 proves pointwise, without division,
--
--   2 (w_tau F_tau) = w_tau i K(n_p,n_q,N_p,u_q)       when p != 0,
--                    = 0                               when p = 0.
--
-- R572 proves for p != 0
--
--   K(P,Q,N_p+N_p,v)
--     = fold_{a+b=p} K(P,Q,M++ + M+- + M-+ + M--,v),
--
-- where the four M terms are exact R106 multiplier-difference vectors and no
-- raw all-inner-helical premise remains.
--
-- Therefore, keeping all integer factors explicit,
--
--   2 * [R438 exhaustive companion cell]
--
-- is exactly one weighted nested componentwise inner fold.  The p=0 branch is
-- zero on both sides and never evaluates normalizedDirection at zero.
--
-- No norm, shell count, Young/Schur step, or spacetime estimate enters.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as R73
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNWeightedProjectedForcingOuterFoldRound438Exact as R438
import DASHI.Physics.Closure.NSTriadKNNestedComponentwiseInnerCommutatorRound572Exact as R572

zeroPlusZero :
  ∀ {r} {F : C3.RealField r} →
  C3.complex3Add (C3.complex3Zero F) (C3.complex3Zero F)
  ≡ C3.complex3Zero F
zeroPlusZero {F = F} =
  Algebra.complex3AddZeroRight (C3.complex3Zero F)

module WeightedNested
    {r} {F : C3.RealField r}
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

  nestedSlotFold :
    (tau : Physical.PhysicalTriadIncidence) → C3.Complex3 F
  nestedSlotFold tau =
    R224.foldVector
      (λ innerTau →
        R145.slotKernel
          (R167.normalizedDirection E S (Physical.p tau))
          (R167.normalizedDirection E S (Physical.q tau))
          (Inner.fourSignInner innerTau)
          (Audit.velocity system (Physical.q tau)))
      (Output.physicalOutputFiber
        (Audit.cutoff system) (Physical.p tau))

  nestedWeightedCompanionCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  nestedWeightedCompanionCell tau
    with Output.modeEqual (Physical.p tau) Z3.zeroMode
  ... | true = C3.complex3Zero F
  ... | false =
    C3.complex3Scale (R294.weight W tau)
      (C3.complex3Scale (C3.complexI F) (nestedSlotFold tau))

  doubleExhaustiveCompanionIsNested :
    (tau : Physical.PhysicalTriadIncidence) →
    C3.complex3Add
      (R438.exhaustiveWeightedCompanionCell W S system tau)
      (R438.exhaustiveWeightedCompanionCell W S system tau)
    ≡ nestedWeightedCompanionCell tau
  doubleExhaustiveCompanionIsNested tau
    with Output.modeEqual (Physical.p tau) Z3.zeroMode in pDecision
  ... | true = zeroPlusZero
  ... | false =
    let
      p = Physical.p tau
      q = Physical.q tau
      P = R167.normalizedDirection E S p
      Q = R167.normalizedDirection E S q
      Np = Audit.projectedNonlinearity system p
      uq = Audit.velocity system q
      w = R294.weight W tau
      slot = R145.slotKernel P Q Np uq

      pNonzero : Z3.NonZeroMode p
      pNonzero = record
        { Z3.notZero = λ pZero →
            Output.falseNotTrue
              (trans (sym pDecision) (Output.modeEqualComplete pZero))
        }

      pullOuterWeight :
        C3.complex3Add
          (C3.complex3Scale w (C3.complex3Scale (C3.complexI F) slot))
          (C3.complex3Scale w (C3.complex3Scale (C3.complexI F) slot))
        ≡
        C3.complex3Scale w
          (C3.complex3Add
            (C3.complex3Scale (C3.complexI F) slot)
            (C3.complex3Scale (C3.complexI F) slot))
      pullOuterWeight =
        sym (R73.complex3ScaleAdd w
          (C3.complex3Scale (C3.complexI F) slot)
          (C3.complex3Scale (C3.complexI F) slot))

      pullI :
        C3.complex3Add
          (C3.complex3Scale (C3.complexI F) slot)
          (C3.complex3Scale (C3.complexI F) slot)
        ≡
        C3.complex3Scale (C3.complexI F)
          (C3.complex3Add slot slot)
      pullI = sym (R73.complex3ScaleAdd (C3.complexI F) slot slot)

      slotAdd :
        C3.complex3Add slot slot
        ≡ R145.slotKernel P Q (C3.complex3Add Np Np) uq
      slotAdd =
        sym (DASHI.Physics.Closure.NSTriadKNNestedProjectedForcingSlotExpansionRound309Exact.slotKernelAdditiveFirstAmplitude
          P Q Np Np uq)

      nested :
        R145.slotKernel P Q (C3.complex3Add Np Np) uq
        ≡ nestedSlotFold tau
      nested =
        Inner.doubledProjectedForcingSlotIsFourSignInnerSlotFold
          P Q uq p pNonzero
    in
    trans pullOuterWeight
      (trans
        (cong (C3.complex3Scale w) pullI)
        (trans
          (cong
            (λ value →
              C3.complex3Scale w
                (C3.complex3Scale (C3.complexI F) value))
            slotAdd)
          (cong
            (λ value →
              C3.complex3Scale w
                (C3.complex3Scale (C3.complexI F) value))
            nested)))

  ----------------------------------------------------------------------
  -- R438's actual weighted R294 cell enters by its exact exhaustive weld.
  ----------------------------------------------------------------------

  fourWeightedR294CellIsNested :
    (tau : Physical.PhysicalTriadIncidence) →
    C3.complex3Add
      (R438.doubleWeightedProjectedForcingCell W S system tau)
      (R438.doubleWeightedProjectedForcingCell W S system tau)
    ≡ nestedWeightedCompanionCell tau
  fourWeightedR294CellIsNested tau =
    trans
      (cong₂ C3.complex3Add
        (R438.doubleWeightedCellIsExhaustiveCompanion
          W system velocityTransverse tau)
        (R438.doubleWeightedCellIsExhaustiveCompanion
          W system velocityTransverse tau))
      (doubleExhaustiveCompanionIsNested tau)

  foldFourWeightedR294IsNested :
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector
      (λ tau → C3.complex3Add
        (R438.doubleWeightedProjectedForcingCell W S system tau)
        (R438.doubleWeightedProjectedForcingCell W S system tau))
      items
    ≡ R224.foldVector nestedWeightedCompanionCell items
  foldFourWeightedR294IsNested [] = refl
  foldFourWeightedR294IsNested (tau ∷ rest) =
    cong₂ C3.complex3Add
      (fourWeightedR294CellIsNested tau)
      (foldFourWeightedR294IsNested rest)

  fixedOutputFourWeightedR294IsNested :
    (output : Z3.FourierMode) →
    R224.foldVector
      (λ tau → C3.complex3Add
        (R438.doubleWeightedProjectedForcingCell W S system tau)
        (R438.doubleWeightedProjectedForcingCell W S system tau))
      (Output.physicalOutputFiber (Audit.cutoff system) output)
    ≡
    R224.foldVector nestedWeightedCompanionCell
      (Output.physicalOutputFiber (Audit.cutoff system) output)
  fixedOutputFourWeightedR294IsNested output =
    foldFourWeightedR294IsNested
      (Output.physicalOutputFiber (Audit.cutoff system) output)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round573R438WeightedCommutatorNestedSameObjectWeldClosed : Bool
round573R438WeightedCommutatorNestedSameObjectWeldClosed = true

round573RawAllInnerHelicalWitnessRequired : Bool
round573RawAllInnerHelicalWitnessRequired = false

round573NormalizedDirectionAtZeroRequired : Bool
round573NormalizedDirectionAtZeroRequired = false

round573DivisionByTwoUsed : Bool
round573DivisionByTwoUsed = false

round573NewAnalyticEstimateIntroduced : Bool
round573NewAnalyticEstimateIntroduced = false

round573SameScaleSummedEstimateClosed : Bool
round573SameScaleSummedEstimateClosed = false

round573ClayPromotion : Bool
round573ClayPromotion = false

round573R438WeightedCommutatorNestedSameObjectWeldClosedIsTrue :
  round573R438WeightedCommutatorNestedSameObjectWeldClosed ≡ true
round573R438WeightedCommutatorNestedSameObjectWeldClosedIsTrue = refl

round573RawAllInnerHelicalWitnessRequiredIsFalse :
  round573RawAllInnerHelicalWitnessRequired ≡ false
round573RawAllInnerHelicalWitnessRequiredIsFalse = refl

round573ClayPromotionIsFalse : round573ClayPromotion ≡ false
round573ClayPromotionIsFalse = refl
