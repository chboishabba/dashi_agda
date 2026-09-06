module DASHI.Analysis.RiemannG2HighestAlphaAfter8894Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2GapSplitClusteringLeanReturn8894Exact as Gap
import DASHI.Analysis.RiemannAristotleQuarterPeriodDensityWindowLeanReturnExact as Q37
import DASHI.Analysis.RiemannAristotleZetaLocalCountLeanReturnExact as Z38
import DASHI.Analysis.RiemannG2AlpogeFurmanClusteringNonDescentExact as AFLocal
import DASHI.Analysis.RiemannG2LowGapClusteringMomentReductionExact as Moment
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
-- HIGHEST-ALPHA SCHEDULER AFTER 8896 + LOCAL-MOMENT REFINEMENT
--
-- This scheduler is updated in place rather than shadowed by a new owner.
-- §37 closes the adaptive J*Lambda constant comparison and §38 closes the zeta
-- upper local-count input.  The live clustering theorem is refined further by
-- the target-local second-moment compiler: highGapMass <= M2_norm < 2*lowGapMass
-- gives a strict two-to-one ratio in Agda; the selected-window analytic moment
-- producer and elementary real coefficient bridge remain unpaid.
--
-- The Alpöge--Furman >2/3 simple/on-critical-line theorem is retained as a
-- global donor but explicitly rejected as a direct local-clustering closure.
--
-- Separate older obligations remain real where their existing owners say so:
-- the selected finite-near evaluator must still be inhabited on the SAME
-- finitePoleNearSigned object, and Gamma producer precision remains independent.
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
  recoverZetaUpperLocalCount
  compareAdaptiveJLambdaConstants
  reuseGlobalSimpleZeroProportionAsLocalClustering
  proveActualZetaLowGapClustering
  proveTargetLocalSecondMoment
  supplyZetaLongWindowLowerDensity

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
leafState recoverZetaUpperLocalCount = owned
leafState compareAdaptiveJLambdaConstants = owned
leafState reuseGlobalSimpleZeroProportionAsLocalClustering = pruned
leafState proveActualZetaLowGapClustering = live
leafState proveTargetLocalSecondMoment = live
leafState supplyZetaLongWindowLowerDensity = conditional

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

zetaUpperCountSearchNoLongerLive :
  Gap.GapSplitRelevant Gap.recoverZetaUpperLocalCount -> ⊥
zetaUpperCountSearchNoLongerLive = Gap.zetaUpperLocalCountSearchPruned

adaptiveConstantComparisonNoLongerLive :
  Gap.GapSplitRelevant Gap.compareQuarterPeriodLowerConstantWithDensityUpperConstant -> ⊥
adaptiveConstantComparisonNoLongerLive = Gap.quarterDensityConstantComparisonPruned

quarterDensityCheckedInLean :
  Q37.machineCheckedInLean Q37.canonicalQuarterPeriodDensityWindowReturn ≡ true
quarterDensityCheckedInLean = refl

zetaShortWindowUpperCountCheckedInLean :
  Z38.zetaShortWindowUpperCountOwnedInLean Z38.canonicalZetaLocalCountLeanReturn ≡ true
zetaShortWindowUpperCountCheckedInLean = refl

actualZetaClusteringStillOpen :
  Z38.actualZetaClusteringClosed Z38.canonicalZetaLocalCountLeanReturn ≡ false
actualZetaClusteringStillOpen = refl

globalSimpleZeroDirectRouteRejected :
  AFLocal.GlobalSimpleToLocalClusteringBoundary.alpogeFurmanDirectlyClosesGapSplitClustering
    AFLocal.canonicalGlobalSimpleToLocalClusteringBoundary ≡ false
globalSimpleZeroDirectRouteRejected = refl

localMomentRatioCompilerOwned :
  Moment.LocalMomentClusteringBoundary.natMomentToTwoToOneRatioCompilerClosedInAgda
    Moment.canonicalLocalMomentClusteringBoundary ≡ true
localMomentRatioCompilerOwned = refl

selectedTargetLocalMomentStillOpen :
  Moment.LocalMomentClusteringBoundary.exactSelectedTargetLocalSecondMomentProducerOwned
    Moment.canonicalLocalMomentClusteringBoundary ≡ false
selectedTargetLocalMomentStillOpen = refl

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
    adaptiveConstantWindowComparisonLiveIsFalse :
      adaptiveConstantWindowComparisonLive ≡ false

    zetaUpperLocalCountStillOpen : Bool
    zetaUpperLocalCountStillOpenIsFalse : zetaUpperLocalCountStillOpen ≡ false

    globalSimpleZeroProportionDirectClusteringRouteLive : Bool
    globalSimpleZeroProportionDirectClusteringRouteLiveIsFalse :
      globalSimpleZeroProportionDirectClusteringRouteLive ≡ false

    actualZetaLowGapClusteringStillRequired : Bool
    actualZetaLowGapClusteringStillRequiredIsTrue :
      actualZetaLowGapClusteringStillRequired ≡ true

    targetLocalSecondMomentRefinementLive : Bool
    targetLocalSecondMomentRefinementLiveIsTrue :
      targetLocalSecondMomentRefinementLive ≡ true

    longWindowLowerDensityStillConditional : Bool
    longWindowLowerDensityStillConditionalIsTrue :
      longWindowLowerDensityStillConditional ≡ true

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
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "After the 8896 return, do not spend effort on adaptive J*Lambda comparison or zeta upper local counting: both are checked Lean outputs wired into the 8894 owner. The global Alpöge--Furman >2/3 simple-zero theorem is not a direct local-clustering closure; an exact finite collision proves that global summary does not determine target-local gap pattern. The shortest concrete clustering refinement is now a SAME-target/SAME-window normalized second-moment theorem strong enough to force highGapMass < 2*lowGapMass; the Agda slack compiler for that implication is owned, while the actual analytic moment producer and elementary 4/pi^2 < 1/2 bridge remain. Existing same-object finite-near evaluation and Gamma-precision obligations remain genuine and must be inhabited rather than duplicated. Final strict budget assembly is downstream; RH remains open."
