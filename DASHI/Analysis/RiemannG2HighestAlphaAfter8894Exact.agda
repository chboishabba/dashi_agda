module DASHI.Analysis.RiemannG2HighestAlphaAfter8894Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2GapSplitClusteringLeanReturn8894Exact as Gap
import DASHI.Analysis.RiemannG2Zeta23FkActionRecoveryExact as Fk
import DASHI.Analysis.RiemannG2Zeta23FkCheckedSourceReturnExact as FkChecked
import DASHI.Analysis.RiemannG2FkOrbitConsumerAttachmentExact as Orbit
import DASHI.Analysis.RiemannG2FkOrbitExplicitFormulaWeldExact as Weld
import DASHI.Analysis.RiemannG2PoleQuotientProducerReconciliation8889Exact as PQ

------------------------------------------------------------------------
-- HIGHEST-ALPHA SCHEDULER AFTER 8894 + CHECKED f_k SOURCE RECOVERY
--
-- Source-side H_A mathematics is already paid on the literal f_k family:
-- character multiplication, paperFT translation, C^2 regularity, support,
-- compact support and continuity.  Backward inspection of the target-centred
-- consumer shows that equality of the WHOLE source function space with the
-- abstract Agda Test carrier is overpayment.  The live representation seam is
-- only the selected source base/target/window orbit embedded into the chosen
-- Weil Test, with admissibility and the same formula's spectral observations.
------------------------------------------------------------------------

data RH8894Leaf : Set where
  searchForModulationOperation
  rebuildCharacterMultiplication
  identifyWholeSourceFunctionSpaceWithWeilTest
  identifyWholeSourceFunctionSpaceWithMellinTest
  recoverSelectedFkOrbitEmbedding
  recoverSelectedFkAdmissibility
  recoverSelectedSameFormulaNearFarSpectralEquality
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
leafState identifyWholeSourceFunctionSpaceWithWeilTest = pruned
leafState identifyWholeSourceFunctionSpaceWithMellinTest = pruned
leafState recoverSelectedFkOrbitEmbedding = live
leafState recoverSelectedFkAdmissibility = live
leafState recoverSelectedSameFormulaNearFarSpectralEquality = live
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
-- Scheduler agreement with existing pruning/source owners.
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

wholeWeilCarrierEqualityNoLongerLive :
  Orbit.PaymentRelevant Orbit.identifyWholeSourceFunctionSpaceWithWeilTest -> ⊥
wholeWeilCarrierEqualityNoLongerLive = Orbit.wholeWeilCarrierEqualityPruned

wholeMellinCarrierEqualityNoLongerLive :
  Orbit.PaymentRelevant Orbit.identifyWholeSourceFunctionSpaceWithMellinTest -> ⊥
wholeMellinCarrierEqualityNoLongerLive = Orbit.wholeMellinCarrierEqualityPruned

genericExplicitFormulaReconstructionNoLongerLive :
  Weld.PaymentRelevant Weld.reconstructGenericExplicitFormula -> ⊥
genericExplicitFormulaReconstructionNoLongerLive =
  Weld.reconstructGenericExplicitFormulaPruned

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

    wholeSourceFunctionSpaceEqualityRequired : Bool
    wholeSourceFunctionSpaceEqualityRequiredIsFalse :
      wholeSourceFunctionSpaceEqualityRequired ≡ false

    selectedFkOrbitEmbeddingStillRequired : Bool
    selectedFkOrbitEmbeddingStillRequiredIsTrue :
      selectedFkOrbitEmbeddingStillRequired ≡ true

    selectedFkAdmissibilityStillRequired : Bool
    selectedFkAdmissibilityStillRequiredIsTrue :
      selectedFkAdmissibilityStillRequired ≡ true

    sameAgdaExplicitFormulaNearFarEqualityStillRequired : Bool
    sameAgdaExplicitFormulaNearFarEqualityStillRequiredIsTrue :
      sameAgdaExplicitFormulaNearFarEqualityStillRequired ≡ true

    crossProverTransportStillRequired : Bool
    crossProverTransportStillRequiredIsTrue : crossProverTransportStillRequired ≡ true

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
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
    "The checked source already owns the literal fk character action, paperFT frequency translation, C^2 regularity, support, compact support and continuity. Backward inspection of the target-centred consumer removes another overpayment: do not identify the entire source C_c^2 function space with the abstract Agda Weil/Mellin Test carrier. Highest-alpha H_A/H_E work is consumer-relative: embed the selected source base/target/window fk orbit into the chosen Weil Test; retain admissibility; transport checked source facts across the prover boundary; and prove the spectralZeroForm of that exact selected test for the same RiemannExplicitFormula is same-ordinate cluster plus finite pole-near signed response plus the same far remainder. The existing explicitFormula theorem then supplies the arithmetic equality automatically. In parallel compare the adaptive J*Lambda constant window or find a different signed near mechanism, repair Gamma precision, attach the owned cluster margin, and pay the final independent budget inequality. RH remains open."
