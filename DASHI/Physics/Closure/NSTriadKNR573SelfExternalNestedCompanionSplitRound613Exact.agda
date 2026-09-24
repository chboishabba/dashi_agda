{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR573SelfExternalNestedCompanionSplitRound613Exact where

------------------------------------------------------------------------
-- ROUND613 / R573 NESTED WEIGHTED COMPANION = SELF + EXTERNAL NETWORK
--
-- R573 identifies its literal nested four-sign cell with TWO copies of R438's
-- exhaustive weighted outer companion.  On the nonzero-p branch R438 is
--
--   w_tau * i * K(P_tau,Q_tau,N_p,u_q).
--
-- Round95 already gives on the same finite Galerkin system
--
--   N_p = N_p^self + N_p^ext.
--
-- Since the slot kernel is additive in its first amplitude, and complex scalar
-- multiplication distributes over vector addition, the R438 companion splits
-- exactly into a selected-self slot and an external-network slot.  Doubling
-- that split and using the existing R573 same-object theorem gives
--
--   nestedWeightedCompanionCell
--     = selfNestedWeightedCompanionCell
--       + externalNestedWeightedCompanionCell.
--
-- The p=0 branch is zero on all three cells.  No norm, absolute value,
-- estimate, shell count, or Clay promotion is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
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
import DASHI.Physics.Closure.NSTriadKNMixedHelicityDampedProductTangentRound231Exact as R231
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNNestedProjectedForcingSlotExpansionRound309Exact as R309
import DASHI.Physics.Closure.NSTriadKNWeightedProjectedForcingOuterFoldRound438Exact as R438
import DASHI.Physics.Closure.NSTriadKNWeightedNestedComponentwiseCommutatorRound573Exact as R573
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadNetworkSplitRound95Exact as R95

zeroPlusZero :
  ∀ {r} {F : C3.RealField r} →
  C3.complex3Add (C3.complex3Zero F) (C3.complex3Zero F)
  ≡ C3.complex3Zero F
zeroPlusZero {F = F} =
  Algebra.complex3AddZeroRight (C3.complex3Zero F)

module NestedNetworkSplit
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

  module Nested = R573.WeightedNested W S L H system velocityTransverse

  velocity = Audit.velocity system

  weightedSelfSlot :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  weightedSelfSlot tau =
    C3.complex3Scale (R294.weight W tau)
      (C3.complex3Scale (C3.complexI F)
        (R145.slotKernel
          (R167.normalizedDirection E S (Physical.p tau))
          (R167.normalizedDirection E S (Physical.q tau))
          (R95.selfForcingP system tau)
          (velocity (Physical.q tau))))

  weightedExternalSlot :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  weightedExternalSlot tau =
    C3.complex3Scale (R294.weight W tau)
      (C3.complex3Scale (C3.complexI F)
        (R145.slotKernel
          (R167.normalizedDirection E S (Physical.p tau))
          (R167.normalizedDirection E S (Physical.q tau))
          (R95.externalForcingP system tau)
          (velocity (Physical.q tau))))

  selfExhaustiveCompanion :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  selfExhaustiveCompanion tau
    with Output.modeEqual (Physical.p tau) Z3.zeroMode
  ... | true = C3.complex3Zero F
  ... | false = weightedSelfSlot tau

  externalExhaustiveCompanion :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  externalExhaustiveCompanion tau
    with Output.modeEqual (Physical.p tau) Z3.zeroMode
  ... | true = C3.complex3Zero F
  ... | false = weightedExternalSlot tau

  weightedSlotSplitsSelfExternal :
    (tau : Physical.PhysicalTriadIncidence) →
    R438.weightedSlotCell W S system tau
    ≡ C3.complex3Add
        (weightedSelfSlot tau)
        (weightedExternalSlot tau)
  weightedSlotSplitsSelfExternal tau =
    let
      p = Physical.p tau
      q = Physical.q tau
      P = R167.normalizedDirection E S p
      Q = R167.normalizedDirection E S q
      self = R95.selfForcingP system tau
      ext = R95.externalForcingP system tau
      uq = velocity q
      w = R294.weight W tau

      fullSplit :
        Audit.projectedNonlinearity system p
        ≡ C3.complex3Add self ext
      fullSplit = R95.fullPIsSelfPlusExternal system tau

      slotSplit :
        R145.slotKernel P Q
          (Audit.projectedNonlinearity system p) uq
        ≡
        C3.complex3Add
          (R145.slotKernel P Q self uq)
          (R145.slotKernel P Q ext uq)
      slotSplit =
        trans
          (cong (λ forcing → R145.slotKernel P Q forcing uq) fullSplit)
          (R309.slotKernelAdditiveFirstAmplitude P Q self ext uq)

      iSplit :
        C3.complex3Scale (C3.complexI F)
          (R145.slotKernel P Q
            (Audit.projectedNonlinearity system p) uq)
        ≡
        C3.complex3Add
          (C3.complex3Scale (C3.complexI F)
            (R145.slotKernel P Q self uq))
          (C3.complex3Scale (C3.complexI F)
            (R145.slotKernel P Q ext uq))
      iSplit =
        trans
          (cong (C3.complex3Scale (C3.complexI F)) slotSplit)
          (R73.complex3ScaleAdd
            (C3.complexI F)
            (R145.slotKernel P Q self uq)
            (R145.slotKernel P Q ext uq))
    in
    trans
      (cong (C3.complex3Scale w) iSplit)
      (R73.complex3ScaleAdd w
        (C3.complex3Scale (C3.complexI F)
          (R145.slotKernel P Q self uq))
        (C3.complex3Scale (C3.complexI F)
          (R145.slotKernel P Q ext uq)))

  exhaustiveCompanionSplitsSelfExternal :
    (tau : Physical.PhysicalTriadIncidence) →
    R438.exhaustiveWeightedCompanionCell W S system tau
    ≡ C3.complex3Add
        (selfExhaustiveCompanion tau)
        (externalExhaustiveCompanion tau)
  exhaustiveCompanionSplitsSelfExternal tau
    with Output.modeEqual (Physical.p tau) Z3.zeroMode
  ... | true = sym zeroPlusZero
  ... | false = weightedSlotSplitsSelfExternal tau

  selfNestedWeightedCompanionCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  selfNestedWeightedCompanionCell tau =
    C3.complex3Add
      (selfExhaustiveCompanion tau)
      (selfExhaustiveCompanion tau)

  externalNestedWeightedCompanionCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  externalNestedWeightedCompanionCell tau =
    C3.complex3Add
      (externalExhaustiveCompanion tau)
      (externalExhaustiveCompanion tau)

  nestedWeightedCompanionSplitsSelfExternal :
    (tau : Physical.PhysicalTriadIncidence) →
    Nested.nestedWeightedCompanionCell tau
    ≡ C3.complex3Add
        (selfNestedWeightedCompanionCell tau)
        (externalNestedWeightedCompanionCell tau)
  nestedWeightedCompanionSplitsSelfExternal tau =
    let
      full = R438.exhaustiveWeightedCompanionCell W S system tau
      self = selfExhaustiveCompanion tau
      ext = externalExhaustiveCompanion tau

      doubledMeaning :
        C3.complex3Add full full
        ≡ Nested.nestedWeightedCompanionCell tau
      doubledMeaning = Nested.doubleExhaustiveCompanionIsNested tau

      splitEach :
        C3.complex3Add full full
        ≡
        C3.complex3Add
          (C3.complex3Add self self)
          (C3.complex3Add ext ext)
      splitEach =
        trans
          (cong₂ C3.complex3Add
            (exhaustiveCompanionSplitsSelfExternal tau)
            (exhaustiveCompanionSplitsSelfExternal tau))
          (R231.complex3RegroupFour self ext self ext)
    in
    trans (sym doubledMeaning) splitEach

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round613R438WeightedSlotSelfExternalSplitClosed : Bool
round613R438WeightedSlotSelfExternalSplitClosed = true

round613R573NestedWeightedCompanionSelfExternalSplitClosed : Bool
round613R573NestedWeightedCompanionSelfExternalSplitClosed = true

round613PreservesR573ZeroModeBranch : Bool
round613PreservesR573ZeroModeBranch = true

round613IntroducesNormOrAbsoluteValue : Bool
round613IntroducesNormOrAbsoluteValue = false

round613IntroducesEstimate : Bool
round613IntroducesEstimate = false

round613ExternalNestedPaymentClosed : Bool
round613ExternalNestedPaymentClosed = false

round613ClayPromotion : Bool
round613ClayPromotion = false

round613R438WeightedSlotSelfExternalSplitClosedIsTrue :
  round613R438WeightedSlotSelfExternalSplitClosed ≡ true
round613R438WeightedSlotSelfExternalSplitClosedIsTrue = refl

round613R573NestedWeightedCompanionSelfExternalSplitClosedIsTrue :
  round613R573NestedWeightedCompanionSelfExternalSplitClosed ≡ true
round613R573NestedWeightedCompanionSelfExternalSplitClosedIsTrue = refl

round613IntroducesEstimateIsFalse :
  round613IntroducesEstimate ≡ false
round613IntroducesEstimateIsFalse = refl

round613ExternalNestedPaymentClosedIsFalse :
  round613ExternalNestedPaymentClosed ≡ false
round613ExternalNestedPaymentClosedIsFalse = refl

round613ClayPromotionIsFalse :
  round613ClayPromotion ≡ false
round613ClayPromotionIsFalse = refl
