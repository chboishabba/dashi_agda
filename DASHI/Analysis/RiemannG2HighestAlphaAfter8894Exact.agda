module DASHI.Analysis.RiemannG2HighestAlphaAfter8894Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2GapSplitClusteringLeanReturn8894Exact as Gap
import DASHI.Analysis.RiemannG2Zeta23FkActionRecoveryExact as Fk
import DASHI.Analysis.RiemannG2Zeta23FkCheckedSourceReturnExact as FkChecked
import DASHI.Analysis.RiemannG2PoleQuotientProducerReconciliation8889Exact as PQ

------------------------------------------------------------------------
-- HIGHEST-ALPHA SCHEDULER AFTER THE 8894 + CHECKED f_k SOURCE AUDIT
--
-- The deeper source audit closes more of H_A than the first 8894 scheduler:
-- Zeta23 itself proves, on the literal f_k family, the paperFT frequency shift,
-- C^2 regularity, support window, compact support and continuity.  Therefore
-- these are not fresh analytic proof-search leaves.  What remains is the
-- same-object/cross-prover attachment into the canonical Agda Weil/Mellin Test
-- and identification with the same Agda RiemannExplicitFormula consumer.
------------------------------------------------------------------------

data RH8894Leaf : Set where
  searchForModulationOperation
  rebuildCharacterMultiplication
  attachSourceFunctionCarrierToCanonicalMellinTest
  proveFkAdmissibilityClosure
  proveFkTransformShift
  identifyFkShiftWithSameExplicitFormula
  transportCheckedFkTheoremsIntoAgda

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
leafState proveFkAdmissibilityClosure = owned
leafState proveFkTransformShift = owned
leafState identifyFkShiftWithSameExplicitFormula = live
leafState transportCheckedFkTheoremsIntoAgda = live

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
-- Proofs that the scheduler agrees with the existing pruning/source owners.
------------------------------------------------------------------------

modulationOperationSearchNoLongerLive :
  Fk.HARelevant Fk.searchForAnyModulationOperation -> ⊥
modulationOperationSearchNoLongerLive = Fk.modulationSearchPruned

sourceShiftReproofNoLongerLive :
  FkChecked.FkSourceRelevant FkChecked.reproveSourcePaperFTShift -> ⊥
sourceShiftReproofNoLongerLive = FkChecked.sourceShiftReproofPruned

sourceContDiffReproofNoLongerLive :
  FkChecked.FkSourceRelevant FkChecked.reproveSourceContDiff -> ⊥
sourceContDiffReproofNoLongerLive = FkChecked.sourceContDiffReproofPruned

sourceCompactSupportReproofNoLongerLive :
  FkChecked.FkSourceRelevant FkChecked.reproveSourceCompactSupport -> ⊥
sourceCompactSupportReproofNoLongerLive = FkChecked.sourceCompactSupportReproofPruned

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
    literalFkActionAlreadyRecoveredIsTrue : literalFkActionAlreadyRecovered ≡ true

    sourceFkPaperFTShiftAlreadyChecked : Bool
    sourceFkPaperFTShiftAlreadyCheckedIsTrue : sourceFkPaperFTShiftAlreadyChecked ≡ true

    sourceFkAnalyticPrerequisitesAlreadyChecked : Bool
    sourceFkAnalyticPrerequisitesAlreadyCheckedIsTrue :
      sourceFkAnalyticPrerequisitesAlreadyChecked ≡ true

    sourceCarrierAttachmentStillRequired : Bool
    sourceCarrierAttachmentStillRequiredIsTrue : sourceCarrierAttachmentStillRequired ≡ true

    crossProverTransportStillRequired : Bool
    crossProverTransportStillRequiredIsTrue : crossProverTransportStillRequired ≡ true

    sameAgdaExplicitFormulaIdentityStillRequired : Bool
    sameAgdaExplicitFormulaIdentityStillRequiredIsTrue :
      sameAgdaExplicitFormulaIdentityStillRequired ≡ true

    sameQuadraticGapSplitRouteStillWorthSharpening : Bool
    sameQuadraticGapSplitRouteStillWorthSharpeningIsFalse :
      sameQuadraticGapSplitRouteStillWorthSharpening ≡ false

    adaptiveConstantWindowComparisonLive : Bool
    adaptiveConstantWindowComparisonLiveIsTrue : adaptiveConstantWindowComparisonLive ≡ true

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
    true refl
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
    "The deeper checked-source audit removes fresh H_A mathematics on the source side: literal f_k character multiplication, paperFT frequency translation, C^2 regularity, support, compact support and continuity are already proved in Zeta23 on the same test family used by its explicit-formula lane. Do not reprove them. Highest-alpha H_A work is now representation/provenance: attach that concrete source family to the canonical Agda Mellin/Weil Test, transport the checked source theorems across the prover boundary, and identify the source explicit-formula response with the same Agda RiemannExplicitFormula instance. In parallel, compare the adaptive J*Lambda constant window or find a genuinely different signed near mechanism, repair Gamma precision, attach the owned cluster margin, then pay the final independent budget inequality. RH remains open."
