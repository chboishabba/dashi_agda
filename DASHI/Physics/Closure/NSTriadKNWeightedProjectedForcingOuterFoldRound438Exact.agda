module DASHI.Physics.Closure.NSTriadKNWeightedProjectedForcingOuterFoldRound438Exact where

------------------------------------------------------------------------
-- ROUND438 / R294 WEIGHTED PROJECTED-FORCING OUTER FOLD IS SLOT-OR-ZERO
--
-- R437 closes the unweighted outer orientation seam on the ACTUAL projected
-- Navier--Stokes forcing:
--
--   p != 0  ->  2 F_pq = i K(n_p,n_q,N_p,u_q),
--   p  = 0  ->  N_p = 0 and 2 F_pq = 0.
--
-- R294 inserts one swap-invariant scalar weight before norms.  This round
-- proves that the same exhaustive classification survives that weighting and
-- finite same-output aggregation exactly.  To avoid any division by two, the
-- theorem keeps R437's doubled cell literally:
--
--   2 (w_tau F_tau)
--     = w_tau [ i K(n_p,n_q,N_p,u_q) ]     when p != 0,
--     = 0                                  when p = 0.
--
-- Folding over the complete physical output fibre therefore gives one exact
-- weighted quadratic-companion sum.  No normalized direction at zero is ever
-- evaluated, and no norm, absolute value, Schur estimate, shell count or
-- spacetime bound is introduced.
--
-- CLAIM BOUNDARY
-- --------------
-- This closes the R294 SAME-OBJECT WEIGHTED FOLD WELD.  It does not estimate
-- that fold.  The remaining R423 leaf is still the cutoff-uniform spacetime
-- bound for the resulting signed quadratic-companion cross.
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
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as R73
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNForcingHelicityCommutatorRound306Exact as R306
import DASHI.Physics.Closure.NSTriadKNForcingSlotKernelRound307Exact as R307
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityZeroOutputRound436Exact as R436
import DASHI.Physics.Closure.NSTriadKNProjectedForcingOuterCellExhaustiveRound437Exact as R437

weightedProjectedForcingCell :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  R294.SwapInvariantCellWeight F →
  (S : Helical.HelicalModeScalars F) →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence →
  C3.Complex3 F
weightedProjectedForcingCell W S system tau =
  R294.weightedCommutatorCell W S
    (Audit.velocity system)
    (Audit.projectedNonlinearity system)
    tau

weightedCommutatorCellIsScaledR230 :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F)
    (tau : Physical.PhysicalTriadIncidence) →
  R294.weightedCommutatorCell W S velocity forcing tau
  ≡ C3.complex3Scale (R294.weight W tau)
      (R230.forcingCommutatorCell S velocity forcing tau)
weightedCommutatorCellIsScaledR230 W S velocity forcing tau =
  sym
    (R73.complex3ScaleSubtract
      (R294.weight W tau)
      (R230.plusForceMinusVelocity S velocity forcing tau)
      (R230.minusForcePlusVelocity S velocity forcing tau))

doubleWeightedProjectedForcingCell :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  R294.SwapInvariantCellWeight F →
  (S : Helical.HelicalModeScalars F) →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence →
  C3.Complex3 F
doubleWeightedProjectedForcingCell W S system tau =
  C3.complex3Add
    (weightedProjectedForcingCell W S system tau)
    (weightedProjectedForcingCell W S system tau)

doubleWeightedCellIsScaledDoubleR230 :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  doubleWeightedProjectedForcingCell W S system tau
  ≡ C3.complex3Scale (R294.weight W tau)
      (R306.doubleR230Cell S
        (Audit.velocity system)
        (Audit.projectedNonlinearity system)
        tau)
doubleWeightedCellIsScaledDoubleR230 W S system tau =
  let
    base =
      R230.forcingCommutatorCell S
        (Audit.velocity system)
        (Audit.projectedNonlinearity system)
        tau
    scaledMeaning =
      weightedCommutatorCellIsScaledR230 W S
        (Audit.velocity system)
        (Audit.projectedNonlinearity system)
        tau
  in
  trans
    (cong₂ C3.complex3Add scaledMeaning scaledMeaning)
    (sym (R73.complex3ScaleAdd (R294.weight W tau) base base))

weightedSlotCell :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  R294.SwapInvariantCellWeight F →
  (S : Helical.HelicalModeScalars F) →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence →
  C3.Complex3 F
weightedSlotCell {F = F} {E = E} W S system tau =
  C3.complex3Scale (R294.weight W tau)
    (C3.complex3Scale (C3.complexI F)
      (R145.slotKernel
        (R167.normalizedDirection E S (Physical.p tau))
        (R167.normalizedDirection E S (Physical.q tau))
        (Audit.projectedNonlinearity system (Physical.p tau))
        (Audit.velocity system (Physical.q tau))))

exhaustiveWeightedCompanionCell :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  R294.SwapInvariantCellWeight F →
  (S : Helical.HelicalModeScalars F) →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence →
  C3.Complex3 F
exhaustiveWeightedCompanionCell {F = F} W S system tau
  with Output.modeEqual (Physical.p tau) Z3.zeroMode
... | true = C3.complex3Zero F
... | false = weightedSlotCell W S system tau

doubleWeightedCellIsExhaustiveCompanion :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {S : Helical.HelicalModeScalars F}
    {L : Helical.PeriodicHelicalProjectorLaws F E I S}
    {H : R142.HelicalHalfCalibration S}
    (W : R294.SwapInvariantCellWeight F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode))
    (tau : Physical.PhysicalTriadIncidence) →
  doubleWeightedProjectedForcingCell W S system tau
  ≡ exhaustiveWeightedCompanionCell W S system tau
doubleWeightedCellIsExhaustiveCompanion {F = F} {E = E} {S = S}
    W system velocityTransverse tau
  with Output.modeEqual (Physical.p tau) Z3.zeroMode in pDecision
... | true =
  let
    pZero = Output.modeEqualSound pDecision
    forcingZero :
      Audit.projectedNonlinearity system (Physical.p tau)
      ≡ C3.complex3Zero F
    forcingZero =
      trans
        (cong (Audit.projectedNonlinearity system) pZero)
        (R436.projectedNonlinearityAtZeroIsZero system velocityTransverse)

    baseZero :
      R306.doubleR230Cell S
        (Audit.velocity system)
        (Audit.projectedNonlinearity system)
        tau
      ≡ C3.complex3Zero F
    baseZero =
      R437.doubleR230ZeroFromForcingZero
        S (Audit.velocity system) (Audit.projectedNonlinearity system)
        tau forcingZero
  in
  trans
    (doubleWeightedCellIsScaledDoubleR230 W S system tau)
    (trans
      (cong (C3.complex3Scale (R294.weight W tau)) baseZero)
      (R106.complex3ScaleZeroVector (R294.weight W tau)))
... | false =
  let
    pNonzero : Z3.NonZeroMode (Physical.p tau)
    pNonzero = record
      { Z3.notZero = λ pZero →
          Output.falseNotTrue
            (trans (sym pDecision) (Output.modeEqualComplete pZero))
      }

    baseSlot :
      R306.doubleR230Cell S
        (Audit.velocity system)
        (Audit.projectedNonlinearity system)
        tau
      ≡
      C3.complex3Scale (C3.complexI F)
        (R145.slotKernel
          (R167.normalizedDirection E S (Physical.p tau))
          (R167.normalizedDirection E S (Physical.q tau))
          (Audit.projectedNonlinearity system (Physical.p tau))
          (Audit.velocity system (Physical.q tau)))
    baseSlot =
      R307.doubledProjectedNSForcingCellIsIOuterSlotKernel
        system tau pNonzero (velocityTransverse (Physical.q tau))
  in
  trans
    (doubleWeightedCellIsScaledDoubleR230 W S system tau)
    (cong (C3.complex3Scale (R294.weight W tau)) baseSlot)

foldDoubleWeightedProjectedForcing :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  R294.SwapInvariantCellWeight F →
  (S : Helical.HelicalModeScalars F) →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Physical.PhysicalTriadIncidence →
  C3.Complex3 F
foldDoubleWeightedProjectedForcing W S system items =
  R224.foldVector
    (doubleWeightedProjectedForcingCell W S system)
    items

foldExhaustiveWeightedCompanion :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  R294.SwapInvariantCellWeight F →
  (S : Helical.HelicalModeScalars F) →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Physical.PhysicalTriadIncidence →
  C3.Complex3 F
foldExhaustiveWeightedCompanion W S system items =
  R224.foldVector
    (exhaustiveWeightedCompanionCell W S system)
    items

foldDoubleWeightedIsExhaustiveCompanion :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {S : Helical.HelicalModeScalars F}
    {L : Helical.PeriodicHelicalProjectorLaws F E I S}
    {H : R142.HelicalHalfCalibration S}
    (W : R294.SwapInvariantCellWeight F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode))
    (items : List Physical.PhysicalTriadIncidence) →
  foldDoubleWeightedProjectedForcing W S system items
  ≡ foldExhaustiveWeightedCompanion W S system items
foldDoubleWeightedIsExhaustiveCompanion W system velocityTransverse [] = refl
foldDoubleWeightedIsExhaustiveCompanion W system velocityTransverse (tau ∷ rest) =
  cong₂ C3.complex3Add
    (doubleWeightedCellIsExhaustiveCompanion
      W system velocityTransverse tau)
    (foldDoubleWeightedIsExhaustiveCompanion
      W system velocityTransverse rest)

fixedOutputDoubleWeightedR294FoldIsQuadraticCompanion :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {S : Helical.HelicalModeScalars F}
    {L : Helical.PeriodicHelicalProjectorLaws F E I S}
    {H : R142.HelicalHalfCalibration S}
    (W : R294.SwapInvariantCellWeight F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode))
    (output : Z3.FourierMode) →
  foldDoubleWeightedProjectedForcing W S system
    (Output.physicalOutputFiber (Audit.cutoff system) output)
  ≡
  foldExhaustiveWeightedCompanion W S system
    (Output.physicalOutputFiber (Audit.cutoff system) output)
fixedOutputDoubleWeightedR294FoldIsQuadraticCompanion
    W system velocityTransverse output =
  foldDoubleWeightedIsExhaustiveCompanion
    W system velocityTransverse
    (Output.physicalOutputFiber (Audit.cutoff system) output)

round438WeightedR294CellIsLiteralWeightedR230Cell : Bool
round438WeightedR294CellIsLiteralWeightedR230Cell = true

round438EveryWeightedOuterCellIsSlotOrZero : Bool
round438EveryWeightedOuterCellIsSlotOrZero = true

round438FixedOutputWeightedSameObjectFoldClosed : Bool
round438FixedOutputWeightedSameObjectFoldClosed = true

round438DivisionByTwoUsed : Bool
round438DivisionByTwoUsed = false

round438NormalizedDirectionAtZeroRequired : Bool
round438NormalizedDirectionAtZeroRequired = false

round438AbsoluteValueIntroduced : Bool
round438AbsoluteValueIntroduced = false

round438WeightedFoldEstimateClosed : Bool
round438WeightedFoldEstimateClosed = false

round438R423SignedCompanionBudgetClosed : Bool
round438R423SignedCompanionBudgetClosed = false

round438PackageAClosed : Bool
round438PackageAClosed = false

round438ClayPromotion : Bool
round438ClayPromotion = false

round438FixedOutputWeightedSameObjectFoldClosedIsTrue :
  round438FixedOutputWeightedSameObjectFoldClosed ≡ true
round438FixedOutputWeightedSameObjectFoldClosedIsTrue = refl

round438DivisionByTwoUsedIsFalse :
  round438DivisionByTwoUsed ≡ false
round438DivisionByTwoUsedIsFalse = refl

round438NormalizedDirectionAtZeroRequiredIsFalse :
  round438NormalizedDirectionAtZeroRequired ≡ false
round438NormalizedDirectionAtZeroRequiredIsFalse = refl

round438WeightedFoldEstimateClosedIsFalse :
  round438WeightedFoldEstimateClosed ≡ false
round438WeightedFoldEstimateClosedIsFalse = refl
