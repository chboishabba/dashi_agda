module DASHI.Analysis.RiemannG2HighestAlphaAfter8894Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2GapSplitClusteringLeanReturn8894Exact as Gap
import DASHI.Analysis.RiemannG2Zeta23FkActionRecoveryExact as Fk
import DASHI.Analysis.RiemannG2Zeta23FkCheckedSourceReturnExact as FkChecked
import DASHI.Analysis.RiemannG2FkOrbitConsumerAttachmentExact as Orbit
import DASHI.Analysis.RiemannG2FkOrbitExplicitFormulaWeldExact as Weld
import DASHI.Analysis.RiemannG2FkSelectedTestSameObjectBidiExact as Same
import DASHI.Analysis.RiemannG2SelectedPoleNearSingleProducerBidiExact as Single
import DASHI.Analysis.RiemannG2SelectedPoleNearFiniteEvaluationSameObjectExact as NearEval
import DASHI.Analysis.RiemannG2GammaProducerSourceAcquisitionExact as GammaSource
import DASHI.Analysis.RiemannG2PoleQuotientProducerReconciliation8889Exact as PQ

------------------------------------------------------------------------
-- HIGHEST-ALPHA SCHEDULER AFTER 8894 + SOURCE-EXACT GAMMA ACQUISITION
--
-- Near side:
--   selected target-window representation = one dependent producer;
--   checked 8883 return owns finite carrier/far shell/cutoff transport;
--   live theorem = phase-preserving finite evaluation on SAME finitePoleNearSigned;
--   after Budget -> selected-Scalar transport, budget extraction is compiler output.
--
-- Gamma side:
--   checked 8889 return owns existence of a coarse uniform bound but not the
--   recovered producer decomposition.  Therefore the current first Gamma leaf
--   is exact source artifact/decomposition recovery, not a guessed analytic
--   sharpening stage.
------------------------------------------------------------------------

data RH8894Leaf : Set where
  searchForModulationOperation
  rebuildCharacterMultiplication
  identifyWholeSourceFunctionSpaceWithWeilTest
  identifyWholeSourceFunctionSpaceWithMellinTest
  separatelyRecoverSelectedFkOrbitAttachment
  separatelyRecoverSelectedNearFarWeld
  separatelyRecoverSelectedSameTestWeld
  recoverActualSelectedPoleNearProducer

  rebuildFiniteNearCarrier
  reproveFarShellDecay
  reproveArbitraryAccuracyCutoff
  recoverPhasePreservingFiniteNearProducer
  weldFiniteNearEvaluationToSelectedWindow
  recoverNearBudgetTransportToSelectedScalar
  extractSelectedNearBudget

  sharpenQuadraticDecayGapSplit
  retuneTaperForGapSplit
  deriveClusteringFromCoarseCounting
  compareAdaptiveJLambdaConstants

  searchForAnyGammaBound
  guessGammaLossWithoutSource
  recoverExactGammaProducerArtifact
  recoverExactGammaProducerDecomposition
  localizeGammaPrecisionLossOnRecoveredProducer
  repairGammaToSharpWindow
  attachOwnedClusterMargin
  combineFinalIndependentBudgets
  : RH8894Leaf

data LeafState : Set where
  pruned owned live conditional downstream : LeafState

leafState : RH8894Leaf -> LeafState
leafState searchForModulationOperation = owned
leafState rebuildCharacterMultiplication = pruned
leafState identifyWholeSourceFunctionSpaceWithWeilTest = pruned
leafState identifyWholeSourceFunctionSpaceWithMellinTest = pruned
leafState separatelyRecoverSelectedFkOrbitAttachment = pruned
leafState separatelyRecoverSelectedNearFarWeld = pruned
leafState separatelyRecoverSelectedSameTestWeld = pruned
leafState recoverActualSelectedPoleNearProducer = live

leafState rebuildFiniteNearCarrier = pruned
leafState reproveFarShellDecay = pruned
leafState reproveArbitraryAccuracyCutoff = pruned
leafState recoverPhasePreservingFiniteNearProducer = live
leafState weldFiniteNearEvaluationToSelectedWindow = live
leafState recoverNearBudgetTransportToSelectedScalar = live
leafState extractSelectedNearBudget = downstream

leafState sharpenQuadraticDecayGapSplit = pruned
leafState retuneTaperForGapSplit = pruned
leafState deriveClusteringFromCoarseCounting = pruned
leafState compareAdaptiveJLambdaConstants = live

leafState searchForAnyGammaBound = pruned
leafState guessGammaLossWithoutSource = pruned
leafState recoverExactGammaProducerArtifact = live
leafState recoverExactGammaProducerDecomposition = live
leafState localizeGammaPrecisionLossOnRecoveredProducer = downstream
leafState repairGammaToSharpWindow = downstream
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

sameObjectWeldIsCompilerOutput :
  Same.PaymentRelevant Same.weldLiteralSelectedTest -> ⊥
sameObjectWeldIsCompilerOutput = Same.literalSelectedTestWeldAlreadyCompiled

sameObjectNearFarAttachmentIsCompilerOutput :
  Same.PaymentRelevant Same.attachNearFarToSameLiteralTest -> ⊥
sameObjectNearFarAttachmentIsCompilerOutput =
  Same.nearFarSameObjectAttachmentAlreadyCompiled

separateSelectedNearFarSearchNoLongerLive :
  Single.searchStatus Single.separatelyRecoverNearFarWeld ≡ Single.pruned
separateSelectedNearFarSearchNoLongerLive = Single.separateNearFarSearchPruned

separateSelectedSameTestSearchNoLongerLive :
  Single.searchStatus Single.separatelyRecoverSameTestWeld ≡ Single.pruned
separateSelectedSameTestSearchNoLongerLive = Single.separateSameTestSearchPruned

finiteNearCarrierRebuildNoLongerLive :
  NearEval.paymentStatus NearEval.rebuildFiniteNearCarrier ≡ NearEval.pruned
finiteNearCarrierRebuildNoLongerLive = NearEval.finiteCarrierRebuildPruned

farShellReproofNoLongerLive :
  NearEval.paymentStatus NearEval.reproveFarShellDecay ≡ NearEval.pruned
farShellReproofNoLongerLive = NearEval.farShellReproofPruned

cutoffReproofNoLongerLive :
  NearEval.paymentStatus NearEval.reproveArbitraryAccuracyCutoff ≡ NearEval.pruned
cutoffReproofNoLongerLive = NearEval.cutoffReproofPruned

nearBudgetExtractionIsDownstream :
  NearEval.paymentStatus NearEval.extractNearBudget ≡ NearEval.downstream
nearBudgetExtractionIsDownstream = NearEval.nearBudgetExtractionIsCompilerOutput

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

guessGammaStirlingLossNoLongerLive :
  GammaSource.SearchRelevant GammaSource.guessStirlingLossWithoutProducer -> ⊥
guessGammaStirlingLossNoLongerLive =
  GammaSource.guessStirlingLossWithoutProducerPruned

guessGammaDigammaLossNoLongerLive :
  GammaSource.SearchRelevant GammaSource.guessDigammaLossWithoutProducer -> ⊥
guessGammaDigammaLossNoLongerLive =
  GammaSource.guessDigammaLossWithoutProducerPruned

gammaSourceRecoveryStageIsArtifactRequired :
  GammaSource.currentGammaProducerRecoveryStage
  ≡ GammaSource.producerArtifactRequired
gammaSourceRecoveryStageIsArtifactRequired = refl

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
    literalFkSourceMathematicsAlreadyRecovered : Bool
    literalFkSourceMathematicsAlreadyRecoveredIsTrue :
      literalFkSourceMathematicsAlreadyRecovered ≡ true

    actualSelectedPoleNearProducerStillRequired : Bool
    actualSelectedPoleNearProducerStillRequiredIsTrue :
      actualSelectedPoleNearProducerStillRequired ≡ true

    finiteNearCarrierAndFarShellFreshMathematicsRequired : Bool
    finiteNearCarrierAndFarShellFreshMathematicsRequiredIsFalse :
      finiteNearCarrierAndFarShellFreshMathematicsRequired ≡ false

    selectedPhasePreservingFiniteEvaluationStillRequired : Bool
    selectedPhasePreservingFiniteEvaluationStillRequiredIsTrue :
      selectedPhasePreservingFiniteEvaluationStillRequired ≡ true

    evaluatorMustBeWeldedToSelectedWindowFiniteNear : Bool
    evaluatorMustBeWeldedToSelectedWindowFiniteNearIsTrue :
      evaluatorMustBeWeldedToSelectedWindowFiniteNear ≡ true

    nearBudgetNeedsOnlyConsumerTransportAfterEvaluation : Bool
    nearBudgetNeedsOnlyConsumerTransportAfterEvaluationIsTrue :
      nearBudgetNeedsOnlyConsumerTransportAfterEvaluation ≡ true

    sameQuadraticGapSplitRouteStillWorthSharpening : Bool
    sameQuadraticGapSplitRouteStillWorthSharpeningIsFalse :
      sameQuadraticGapSplitRouteStillWorthSharpening ≡ false

    adaptiveConstantWindowComparisonLive : Bool
    adaptiveConstantWindowComparisonLiveIsTrue :
      adaptiveConstantWindowComparisonLive ≡ true

    exactGammaProducerArtifactRecoveryLive : Bool
    exactGammaProducerArtifactRecoveryLiveIsTrue :
      exactGammaProducerArtifactRecoveryLive ≡ true

    sourceFreeGammaLossGuessAdmissible : Bool
    sourceFreeGammaLossGuessAdmissibleIsFalse :
      sourceFreeGammaLossGuessAdmissible ≡ false

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
    false refl
    true refl
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "The zero-side lane is now one dependent selected target-window producer plus one phase-preserving finite-near evaluator on the SAME finitePoleNearSigned scalar. Checked 8883 owns finite carrier/far shell/cutoff transport. After the evaluator is welded to the selected finite-near value, only a consumer-relative transport from its abstract Budget to the selected Weil scalar is needed; selected near-budget extraction is compiler output. For Gamma, the stronger existing source-acquisition owner supersedes a free-floating candidate-stage search: currentGammaProducerRecoveryStage is producerArtifactRequired. Recover the exact checked uniform-bound artifact and decomposition first, then localize the first source-verified precision loss and repair that step. Source-free Stirling/digamma guesses are pruned. The adaptive J*Lambda constant-window comparison and final same-scalar/same-taper strict budget assembly remain live. RH remains open."
