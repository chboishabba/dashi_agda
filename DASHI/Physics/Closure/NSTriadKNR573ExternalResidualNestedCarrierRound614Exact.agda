{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR573ExternalResidualNestedCarrierRound614Exact where

------------------------------------------------------------------------
-- ROUND614 / R573 EXTERNAL NESTED COMPONENT ON THE LITERAL R112 RESIDUAL
--
-- R613 proves pointwise
--
--   NestedFull_tau = NestedSelf_tau + NestedExternal_tau.
--
-- This owner does two finite representation steps:
--
-- (1) lift that pointwise identity through an arbitrary finite outer fold;
--
-- (2) whenever R112's existing ThreeLegResidualMembership witness is supplied
--     for tau, identify NestedExternal_tau with the SAME weighted slot built
--     from R112.externalResidualP.
--
-- No global witness family is invented.  No norm, absolute value, estimate,
-- Bony bound, shell count, or Clay promotion is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeResidualCarrierRound112Exact as R112
import DASHI.Physics.Closure.NSTriadKNR573SelfExternalNestedCompanionSplitRound613Exact as R613

module ExternalNestedResidual
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

  module Split =
    R613.NestedNetworkSplit W S L H system velocityTransverse

  velocity = Audit.velocity system

  weightedExternalResidualSlot :
    (tau : Physical.PhysicalTriadIncidence) →
    R112.ThreeLegResidualMembership system tau →
    C3.Complex3 F
  weightedExternalResidualSlot tau M =
    C3.complex3Scale (R294.weight W tau)
      (C3.complex3Scale (C3.complexI F)
        (R145.slotKernel
          (R167.normalizedDirection E S (Physical.p tau))
          (R167.normalizedDirection E S (Physical.q tau))
          (R112.externalResidualP system tau M)
          (velocity (Physical.q tau))))

  weightedExternalSlotIsLiteralResidual :
    (tau : Physical.PhysicalTriadIncidence) →
    (M : R112.ThreeLegResidualMembership system tau) →
    Split.weightedExternalSlot tau
    ≡ weightedExternalResidualSlot tau M
  weightedExternalSlotIsLiteralResidual tau M =
    cong
      (C3.complex3Scale (R294.weight W tau))
      (cong
        (C3.complex3Scale (C3.complexI F))
        (cong
          (λ forcing →
            R145.slotKernel
              (R167.normalizedDirection E S (Physical.p tau))
              (R167.normalizedDirection E S (Physical.q tau))
              forcing
              (velocity (Physical.q tau)))
          (R112.externalForcingPIsResidual system tau M)))

  externalResidualExhaustiveCompanion :
    (tau : Physical.PhysicalTriadIncidence) →
    R112.ThreeLegResidualMembership system tau →
    C3.Complex3 F
  externalResidualExhaustiveCompanion tau M
    with Output.modeEqual (Physical.p tau) Z3.zeroMode
  ... | true = C3.complex3Zero F
  ... | false = weightedExternalResidualSlot tau M

  externalExhaustiveCompanionIsLiteralResidual :
    (tau : Physical.PhysicalTriadIncidence) →
    (M : R112.ThreeLegResidualMembership system tau) →
    Split.externalExhaustiveCompanion tau
    ≡ externalResidualExhaustiveCompanion tau M
  externalExhaustiveCompanionIsLiteralResidual tau M
    with Output.modeEqual (Physical.p tau) Z3.zeroMode
  ... | true = refl
  ... | false = weightedExternalSlotIsLiteralResidual tau M

  externalResidualNestedWeightedCompanionCell :
    (tau : Physical.PhysicalTriadIncidence) →
    R112.ThreeLegResidualMembership system tau →
    C3.Complex3 F
  externalResidualNestedWeightedCompanionCell tau M =
    C3.complex3Add
      (externalResidualExhaustiveCompanion tau M)
      (externalResidualExhaustiveCompanion tau M)

  externalNestedWeightedCompanionIsLiteralResidual :
    (tau : Physical.PhysicalTriadIncidence) →
    (M : R112.ThreeLegResidualMembership system tau) →
    Split.externalNestedWeightedCompanionCell tau
    ≡ externalResidualNestedWeightedCompanionCell tau M
  externalNestedWeightedCompanionIsLiteralResidual tau M =
    cong₂ C3.complex3Add
      (externalExhaustiveCompanionIsLiteralResidual tau M)
      (externalExhaustiveCompanionIsLiteralResidual tau M)

  foldPointwiseEqual :
    (left right :
      Physical.PhysicalTriadIncidence → C3.Complex3 F) →
    ((tau : Physical.PhysicalTriadIncidence) → left tau ≡ right tau) →
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector left items ≡ R224.foldVector right items
  foldPointwiseEqual left right pointwise [] = refl
  foldPointwiseEqual left right pointwise (tau ∷ rest) =
    cong₂ C3.complex3Add
      (pointwise tau)
      (foldPointwiseEqual left right pointwise rest)

  finiteNestedFoldSplitsSelfExternal :
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector Split.Nested.nestedWeightedCompanionCell items
    ≡
    C3.complex3Add
      (R224.foldVector Split.selfNestedWeightedCompanionCell items)
      (R224.foldVector Split.externalNestedWeightedCompanionCell items)
  finiteNestedFoldSplitsSelfExternal items =
    trans
      (foldPointwiseEqual
        Split.Nested.nestedWeightedCompanionCell
        (λ tau →
          C3.complex3Add
            (Split.selfNestedWeightedCompanionCell tau)
            (Split.externalNestedWeightedCompanionCell tau))
        Split.nestedWeightedCompanionSplitsSelfExternal
        items)
      (R225.foldPointwiseAdd
        Split.selfNestedWeightedCompanionCell
        Split.externalNestedWeightedCompanionCell
        items)

  fixedOutputNestedFoldSplitsSelfExternal :
    (output : Z3.FourierMode) →
    R224.foldVector Split.Nested.nestedWeightedCompanionCell
      (Output.physicalOutputFiber (Audit.cutoff system) output)
    ≡
    C3.complex3Add
      (R224.foldVector Split.selfNestedWeightedCompanionCell
        (Output.physicalOutputFiber (Audit.cutoff system) output))
      (R224.foldVector Split.externalNestedWeightedCompanionCell
        (Output.physicalOutputFiber (Audit.cutoff system) output))
  fixedOutputNestedFoldSplitsSelfExternal output =
    finiteNestedFoldSplitsSelfExternal
      (Output.physicalOutputFiber (Audit.cutoff system) output)

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round614ExternalNestedCellOnLiteralR112ResidualClosed : Bool
round614ExternalNestedCellOnLiteralR112ResidualClosed = true

round614FiniteR573FoldSelfExternalSplitClosed : Bool
round614FiniteR573FoldSelfExternalSplitClosed = true

round614FixedOutputR573FoldSelfExternalSplitClosed : Bool
round614FixedOutputR573FoldSelfExternalSplitClosed = true

round614CanonicalResidualWitnessFamilyInstalled : Bool
round614CanonicalResidualWitnessFamilyInstalled = false

round614ExternalNestedPaymentClosed : Bool
round614ExternalNestedPaymentClosed = false

round614IntroducesEstimate : Bool
round614IntroducesEstimate = false

round614ClayPromotion : Bool
round614ClayPromotion = false

round614ExternalNestedCellOnLiteralR112ResidualClosedIsTrue :
  round614ExternalNestedCellOnLiteralR112ResidualClosed ≡ true
round614ExternalNestedCellOnLiteralR112ResidualClosedIsTrue = refl

round614FiniteR573FoldSelfExternalSplitClosedIsTrue :
  round614FiniteR573FoldSelfExternalSplitClosed ≡ true
round614FiniteR573FoldSelfExternalSplitClosedIsTrue = refl

round614FixedOutputR573FoldSelfExternalSplitClosedIsTrue :
  round614FixedOutputR573FoldSelfExternalSplitClosed ≡ true
round614FixedOutputR573FoldSelfExternalSplitClosedIsTrue = refl

round614CanonicalResidualWitnessFamilyInstalledIsFalse :
  round614CanonicalResidualWitnessFamilyInstalled ≡ false
round614CanonicalResidualWitnessFamilyInstalledIsFalse = refl

round614ExternalNestedPaymentClosedIsFalse :
  round614ExternalNestedPaymentClosed ≡ false
round614ExternalNestedPaymentClosedIsFalse = refl

round614IntroducesEstimateIsFalse :
  round614IntroducesEstimate ≡ false
round614IntroducesEstimateIsFalse = refl

round614ClayPromotionIsFalse :
  round614ClayPromotion ≡ false
round614ClayPromotionIsFalse = refl
