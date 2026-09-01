module DASHI.Analysis.RiemannG2HighestAlphaAfter8894Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2GapSplitClusteringLeanReturn8894Exact as Gap
import DASHI.Analysis.RiemannG2Zeta23FkActionRecoveryExact as Fk
import DASHI.Analysis.RiemannG2PoleQuotientProducerReconciliation8889Exact as PQ

------------------------------------------------------------------------
-- HIGHEST-ALPHA SCHEDULER AFTER THE 8894 LEAN RETURN
--
-- This owner is deliberately consumer-relative.  It prevents search from
-- reopening leaves that are now either source-owned or theorem-level pruned.
--
-- Zero-side/H_A:
--   * literal target-character multiplication fk is source-owned;
--   * carrier attachment, admissibility, and proof-relevant shift remain live.
--
-- Near/crossing/H_E:
--   * narrow cancellation is impossible;
--   * quadratic-decay gap-split sharpening and taper retuning are pruned;
--   * coarse counting cannot manufacture the needed clustering;
--   * adaptive inverse-width scaling itself is NOT refuted, so compare the
--     lower quarter-period constant against the upper density constant.
--
-- Gamma:
--   * existence of some Gamma bound is already owned;
--   * only sharp precision repair remains live.
------------------------------------------------------------------------

data RH8894Leaf : Set where
  searchForModulationOperation
  rebuildCharacterMultiplication
  attachSourceFunctionCarrierToCanonicalMellinTest
  proveFkAdmissibilityClosure
  proveFkTransformShift
  identifyFkShiftWithSameExplicitFormula

  sharpenQuadraticDecayGapSplit
  retuneTaperForGapSplit
  deriveClusteringFromCoarseCounting
  compareAdaptiveJLambdaConstants
  seekDifferentSignedNearMechanism

  searchForAnyGammaBound
  repairGammaToSharpWindow
  attachOwnedClusterMargin
  combineFinalIndependentBudgets
  : RH8894Leaf

data LeafState : Set where
  pruned owned live conditional : LeafState

leafState : RH8894Leaf -> LeafState
leafState searchForModulationOperation = owned
leafState rebuildCharacterMultiplication = pruned
leafState attachSourceFunctionCarrierToCanonicalMellinTest = live
leafState proveFkAdmissibilityClosure = live
leafState proveFkTransformShift = live
leafState identifyFkShiftWithSameExplicitFormula = live

leafState sharpenQuadraticDecayGapSplit = pruned
leafState retuneTaperForGapSplit = pruned
leafState deriveClusteringFromCoarseCounting = pruned
leafState compareAdaptiveJLambdaConstants = live
leafState seekDifferentSignedNearMechanism = live

leafState searchForAnyGammaBound = pruned
leafState repairGammaToSharpWindow = live
leafState attachOwnedClusterMargin = live
leafState combineFinalIndependentBudgets = conditional

------------------------------------------------------------------------
-- Proofs that the scheduler agrees with the existing pruning owners.
------------------------------------------------------------------------

modulationOperationSearchNoLongerLive :
  Fk.HARelevant Fk.searchForAnyModulationOperation -> ⊥
modulationOperationSearchNoLongerLive = Fk.modulationSearchPruned

quadraticGapSplitSharpeningNoLongerLive :
  Gap.GapSplitRelevant Gap.sharpenSameQuadraticDecayDonor -> ⊥
quadraticGapSplitSharpeningNoLongerLive = Gap.sameQuadraticDecayDonorPruned

taperGapSplitRetuningNoLongerLive :
  Gap.GapSplitRelevant Gap.retuneTaperWidthOrProfile -> ⊥
taperGapSplitRetuningNoLongerLive = Gap.taperRetuningPruned

coarseCountingClusteringNoLongerLive :
  Gap.GapSplitRelevant Gap.deriveClusteringFromCoarseCountingOnly -> ⊥
coarseCountingClusteringNoLongerLive = Gap.coarseCountingClusteringPruned

genericGammaSearchNoLongerLive :
  PQ.LeafRelevant PQ.findAnyGammaUpperBound -> ⊥
genericGammaSearchNoLongerLive = PQ.findAnyGammaUpperBoundPruned

adaptiveInverseWidthStillLogicallyOpen :
  Gap.densityCutRefutesEveryAdaptiveInverseWidthRoute
    Gap.canonicalGapSplitClusteringLeanReturn8894 ≡ false
adaptiveInverseWidthStillLogicallyOpen =
  Gap.densityCutRefutesEveryAdaptiveInverseWidthRouteIsFalse
    Gap.canonicalGapSplitClusteringLeanReturn8894

------------------------------------------------------------------------
-- Frontier receipt.
------------------------------------------------------------------------

record HighestAlphaAfter8894Boundary : Set where
  constructor highest-alpha-after-8894-boundary
  field
    literalFkActionAlreadyRecovered : Bool
    literalFkActionAlreadyRecoveredIsTrue :
      literalFkActionAlreadyRecovered ≡ true

    sourceCarrierAttachmentStillRequired : Bool
    sourceCarrierAttachmentStillRequiredIsTrue :
      sourceCarrierAttachmentStillRequired ≡ true

    sourceTransformShiftProofStillRequired : Bool
    sourceTransformShiftProofStillRequiredIsTrue :
      sourceTransformShiftProofStillRequired ≡ true

    sameQuadraticGapSplitRouteStillWorthSharpening : Bool
    sameQuadraticGapSplitRouteStillWorthSharpeningIsFalse :
      sameQuadraticGapSplitRouteStillWorthSharpening ≡ false

    adaptiveConstantWindowComparisonLive : Bool
    adaptiveConstantWindowComparisonLiveIsTrue :
      adaptiveConstantWindowComparisonLive ≡ true

    gammaPrecisionRepairLive : Bool
    gammaPrecisionRepairLiveIsTrue : gammaPrecisionRepairLive ≡ true

    finalBudgetCombinationAlreadyUnconditional : Bool
    finalBudgetCombinationAlreadyUnconditionalIsFalse :
      finalBudgetCombinationAlreadyUnconditional ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalHighestAlphaAfter8894Boundary : HighestAlphaAfter8894Boundary
canonicalHighestAlphaAfter8894Boundary =
  highest-alpha-after-8894-boundary
    true refl
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
    "After the 8894 return, do not search for another modulation operation and do not sharpen the same quadratic-decay gap split. The literal Zeta23 fk character multiplication is already recovered. Highest-alpha work is: attach that source function carrier to the canonical Mellin Test; recover/prove its admissibility and transform/same-formula shift receipts; compare the quarter-period lower constant with the 8894 density upper constant in the adaptive inverse-width regime or find a genuinely different signed near mechanism; repair Gamma to the sharp consumer window; attach the already-owned quantitative cluster margin; then pay the final independent strict budget inequality. RH remains open."
