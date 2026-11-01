module DASHI.Physics.Closure.NSTriadKNNestedComponentwiseInnerCommutatorRound572Exact where

------------------------------------------------------------------------
-- ROUND572 / REMOVE THE RAW ALL-INNER-HELICAL PREMISE FROM R435
--
-- R571 proves for every physical inner pair a+b=p with p != 0 that the raw
-- paired Galerkin interaction equals the sum of four helical sign-pair
-- multiplier-difference vectors.  R310 already proves unconditionally
--
--   N_p + N_p = fold_{a+b=p} pairedInnerVector.
--
-- Therefore the complete inner fibre can be rewritten pointwise by R571,
-- without assuming that the raw physical velocity is itself a curl eigenfield.
-- R309/R435's generic finite additivity then pushes the resulting SAME inner
-- sum through the outer R145 slot kernel before norms.
--
-- Result:
--
--   K(P,Q,N_p+N_p,v)
--     = fold_{a+b=p} K(P,Q, M++ + M+- + M-+ + M-- , v)
--
-- where each Mst is R571's exact R106 multiplier-difference vector.
--
-- No shell estimate, norm, cardinality factor, or spacetime bound is added.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNNestedProjectedForcingSlotExpansionRound309Exact as R309
import DASHI.Physics.Closure.NSTriadKNNestedInnerSwapCommutatorRound310Exact as R310
import DASHI.Physics.Closure.NSTriadKNNestedInnerForcingAggregationRound435Exact as R435
import DASHI.Physics.Closure.NSTriadKNInnerHelicalComponentCommutatorRound571Exact as R571

module ComponentwiseNested
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module C = R571.Componentwise system S L velocityTransverse

  fourSignInner :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  fourSignInner tau =
    C3.complex3Add
      (C3.complex3Add
        (C.multiplierDifferenceVector tau Helical.plus Helical.plus)
        (C.multiplierDifferenceVector tau Helical.plus Helical.minus))
      (C3.complex3Add
        (C.multiplierDifferenceVector tau Helical.minus Helical.plus)
        (C.multiplierDifferenceVector tau Helical.minus Helical.minus))

  outputNonzeroForMember :
    (p : Z3.FourierMode) →
    Z3.NonZeroMode p →
    (tau : Physical.PhysicalTriadIncidence) →
    tau Cube.∈ Output.physicalOutputFiber (Audit.cutoff system) p →
    Z3.NonZeroMode (Physical.k tau)
  outputNonzeroForMember p pNonzero tau member = record
    { Z3.notZero = λ kZero →
        Z3.notZero pNonzero
          (trans
            (sym (Output.physicalOutputFiberSound member))
            kZero)
    }

  pairedInnerPointwise :
    (p : Z3.FourierMode) →
    (pNonzero : Z3.NonZeroMode p) →
    (tau : Physical.PhysicalTriadIncidence) →
    tau Cube.∈ Output.physicalOutputFiber (Audit.cutoff system) p →
    R310.pairedInnerVector system tau ≡ fourSignInner tau
  pairedInnerPointwise p pNonzero tau member =
    C.partnerVectorSumIsFourMultiplierDifferences tau
      (outputNonzeroForMember p pNonzero tau member)

  foldPairedInnerIsFourSignInner :
    (p : Z3.FourierMode) →
    (pNonzero : Z3.NonZeroMode p) →
    (items : List Physical.PhysicalTriadIncidence) →
    ((tau : Physical.PhysicalTriadIncidence) →
      tau Cube.∈ items →
      tau Cube.∈ Output.physicalOutputFiber (Audit.cutoff system) p) →
    R224.foldVector (R310.pairedInnerVector system) items
    ≡ R224.foldVector fourSignInner items
  foldPairedInnerIsFourSignInner p pNonzero [] included = refl
  foldPairedInnerIsFourSignInner p pNonzero (tau ∷ rest) included =
    cong₂ C3.complex3Add
      (pairedInnerPointwise p pNonzero tau
        (included tau (Cube.here refl)))
      (foldPairedInnerIsFourSignInner p pNonzero rest
        (λ beta member → included beta (Cube.there member)))

  completeInnerFoldIsFourSignInner :
    (p : Z3.FourierMode) →
    (pNonzero : Z3.NonZeroMode p) →
    R224.foldVector (R310.pairedInnerVector system)
      (Output.physicalOutputFiber (Audit.cutoff system) p)
    ≡
    R224.foldVector fourSignInner
      (Output.physicalOutputFiber (Audit.cutoff system) p)
  completeInnerFoldIsFourSignInner p pNonzero =
    foldPairedInnerIsFourSignInner p pNonzero
      (Output.physicalOutputFiber (Audit.cutoff system) p)
      (λ tau member → member)

  twiceProjectedNonlinearityIsFourSignInnerFold :
    (p : Z3.FourierMode) →
    (pNonzero : Z3.NonZeroMode p) →
    C3.complex3Add
      (Audit.projectedNonlinearity system p)
      (Audit.projectedNonlinearity system p)
    ≡
    R224.foldVector fourSignInner
      (Output.physicalOutputFiber (Audit.cutoff system) p)
  twiceProjectedNonlinearityIsFourSignInnerFold p pNonzero =
    trans
      (R310.twiceProjectedNonlinearityIsPairedInnerFold system p)
      (completeInnerFoldIsFourSignInner p pNonzero)

  ----------------------------------------------------------------------
  -- Push the complete componentwise inner normal form through the outer slot.
  ----------------------------------------------------------------------

  doubledProjectedForcingSlotIsFourSignInnerSlotFold :
    (P Q v : C3.Complex3 F)
    (p : Z3.FourierMode) →
    (pNonzero : Z3.NonZeroMode p) →
    R145.slotKernel P Q
      (C3.complex3Add
        (Audit.projectedNonlinearity system p)
        (Audit.projectedNonlinearity system p))
      v
    ≡
    R224.foldVector
      (λ tau → R145.slotKernel P Q (fourSignInner tau) v)
      (Output.physicalOutputFiber (Audit.cutoff system) p)
  doubledProjectedForcingSlotIsFourSignInnerSlotFold
      P Q v p pNonzero =
    let
      items = Output.physicalOutputFiber (Audit.cutoff system) p
    in
    trans
      (cong
        (λ forcing → R145.slotKernel P Q forcing v)
        (twiceProjectedNonlinearityIsFourSignInnerFold p pNonzero))
      (trans
        (cong
          (λ forcing → R145.slotKernel P Q forcing v)
          (R435.foldVectorAsSumMap fourSignInner items))
        (trans
          (R309.slotKernelFoldFirstAmplitude
            P Q v (map fourSignInner items))
          (trans
            (cong Audit.sumVectors
              (R435.mapSlotAfterInner P Q v fourSignInner items))
            (sym
              (R435.foldVectorAsSumMap
                (λ tau → R145.slotKernel P Q (fourSignInner tau) v)
                items)))))

------------------------------------------------------------------------
-- Dependency correction relative to the historical R435 route.
------------------------------------------------------------------------

round572CompleteInnerComponentwiseNormalFormClosed : Bool
round572CompleteInnerComponentwiseNormalFormClosed = true

round572OuterSlotAggregationWithoutRawHelicalPremiseClosed : Bool
round572OuterSlotAggregationWithoutRawHelicalPremiseClosed = true

round572RawAllInnerHelicalWitnessRequired : Bool
round572RawAllInnerHelicalWitnessRequired = false

round572OrbitDivisionOrCardinalityFactorIntroduced : Bool
round572OrbitDivisionOrCardinalityFactorIntroduced = false

round572RequiresNonzeroOuterPForMultiplierDifferenceNormalForm : Bool
round572RequiresNonzeroOuterPForMultiplierDifferenceNormalForm = true

round572ZeroOuterPHandledHere : Bool
round572ZeroOuterPHandledHere = false

round572SameScaleSummedEstimateClosed : Bool
round572SameScaleSummedEstimateClosed = false

round572ClayPromotion : Bool
round572ClayPromotion = false

round572CompleteInnerComponentwiseNormalFormClosedIsTrue :
  round572CompleteInnerComponentwiseNormalFormClosed ≡ true
round572CompleteInnerComponentwiseNormalFormClosedIsTrue = refl

round572RawAllInnerHelicalWitnessRequiredIsFalse :
  round572RawAllInnerHelicalWitnessRequired ≡ false
round572RawAllInnerHelicalWitnessRequiredIsFalse = refl

round572SameScaleSummedEstimateClosedIsFalse :
  round572SameScaleSummedEstimateClosed ≡ false
round572SameScaleSummedEstimateClosedIsFalse = refl

round572ClayPromotionIsFalse : round572ClayPromotion ≡ false
round572ClayPromotionIsFalse = refl
