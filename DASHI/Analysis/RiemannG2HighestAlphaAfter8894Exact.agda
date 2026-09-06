module DASHI.Analysis.RiemannG2HighestAlphaAfter8894Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2GapSplitClusteringLeanReturn8894Exact as Gap
import DASHI.Analysis.RiemannAristotleQuarterPeriodDensityWindowLeanReturnExact as Q37
import DASHI.Analysis.RiemannAristotleZetaLocalCountLeanReturnExact as Z38
import DASHI.Analysis.RiemannG2AlpogeFurmanClusteringNonDescentExact as AFLocal
import DASHI.Analysis.RiemannG2LowGapClusteringMomentReductionExact as Moment
import DASHI.Analysis.RiemannG2SelectedDirectFiniteMomentBidiExact as Shared
import DASHI.Analysis.RiemannAristotlePoleNearPhaseStatisticExact as Phase
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
-- HIGHEST-ALPHA SCHEDULER AFTER 8896 + SHARED DIRECT-CARRIER REFINEMENT
--
-- §37 closes the adaptive J*Lambda comparison and §38 closes zeta upper local
-- counting. The live clustering consumer is refined by a target-local ordinate
-- moment, but the dependency order is now explicit:
--
--   recover ActualSelectedPoleNearProducer             LIVE
--   recover DirectFinitePoleNearProducer               LIVE
--      -> SelectedDirectFiniteWeld                     DOWNSTREAM
--          -> selected delta^2 moment                  DOWNSTREAM
--          -> selected finite-near consumer attachment DOWNSTREAM
--
-- DirectFinitePoleNearProducer already carries targetRelativeGap and its signed
-- approximant/error receipt. Consequently PoleNearPhaseStatistic is compiler
-- output and a second phase carrier is pruned. The moment compiler itself is
-- also already owned; what is unpaid is the actual selected/direct producer data
-- and quantitative moment/evaluation strength.
--
-- Direct proof of the clustering inequality remains an independent live route.
-- Gamma producer recovery remains independent.
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
  constructSecondPhaseStatisticCarrier
  recoverDirectFinitePoleNearProducer
  weldSelectedDirectZeroCarrier
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
leafState constructSecondPhaseStatisticCarrier = pruned
leafState recoverDirectFinitePoleNearProducer = live
leafState weldSelectedDirectZeroCarrier = downstream
leafState weldFiniteNearEvaluationToSelectedWindow = downstream
leafState recoverNearBudgetTransportToSelectedScalar = downstream
leafState extractSelectedNearBudget = downstream

leafState sharpenQuadraticDecayGapSplit = pruned
leafState retuneTaperForGapSplit = pruned
leafState deriveClusteringFromCoarseCounting = pruned
leafState recoverZetaUpperLocalCount = owned
leafState compareAdaptiveJLambdaConstants = owned
leafState reuseGlobalSimpleZeroProportionAsLocalClustering = pruned
leafState proveActualZetaLowGapClustering = live
leafState proveTargetLocalSecondMoment = downstream
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

secondPhaseStatisticCarrierNoLongerLive :
  Phase.paymentState Phase.constructSecondPhaseStatisticCarrier ≡ Phase.pruned
secondPhaseStatisticCarrierNoLongerLive = Phase.secondPhaseStatisticCarrierPruned

phaseStatisticCompilerOwned :
  Phase.PoleNearPhaseStatisticBoundary.repositoryAlreadyOwnsConcretePoleNearPhaseStatistic
    Phase.canonicalPoleNearPhaseStatisticBoundary ≡ true
phaseStatisticCompilerOwned = refl

selectedDirectWeldStillOpen :
  Shared.SelectedDirectFiniteMomentBoundary.selectedDirectWeldInhabitedHere
    Shared.canonicalSelectedDirectFiniteMomentBoundary ≡ false
selectedDirectWeldStillOpen = refl

sharedDirectCarrierCanFeedBoth :
  Shared.SelectedDirectFiniteMomentBoundary.oneDirectGapCarrierCanFeedClusteringAndFiniteEvaluation
    Shared.canonicalSelectedDirectFiniteMomentBoundary ≡ true
sharedDirectCarrierCanFeedBoth = refl

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
  GammaSource.currentGammaProducerRecoveryStage ≡ GammaSource.producerArtifactRequired
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
    literalFkSourceMathematicsAlreadyRecoveredIsTrue : literalFkSourceMathematicsAlreadyRecovered ≡ true

    actualSelectedPoleNearProducerStillRequired : Bool
    actualSelectedPoleNearProducerStillRequiredIsTrue : actualSelectedPoleNearProducerStillRequired ≡ true

    directFinitePoleNearProducerStillRequired : Bool
    directFinitePoleNearProducerStillRequiredIsTrue : directFinitePoleNearProducerStillRequired ≡ true

    finiteNearCarrierAndFarShellFreshMathematicsRequired : Bool
    finiteNearCarrierAndFarShellFreshMathematicsRequiredIsFalse : finiteNearCarrierAndFarShellFreshMathematicsRequired ≡ false

    secondPhaseStatisticCarrierRequired : Bool
    secondPhaseStatisticCarrierRequiredIsFalse : secondPhaseStatisticCarrierRequired ≡ false

    selectedDirectWeldIsDownstreamOfBothProducers : Bool
    selectedDirectWeldIsDownstreamOfBothProducersIsTrue : selectedDirectWeldIsDownstreamOfBothProducers ≡ true

    selectedPhasePreservingFiniteEvaluationStillRequired : Bool
    selectedPhasePreservingFiniteEvaluationStillRequiredIsTrue : selectedPhasePreservingFiniteEvaluationStillRequired ≡ true

    nearBudgetNeedsOnlyConsumerTransportAfterEvaluation : Bool
    nearBudgetNeedsOnlyConsumerTransportAfterEvaluationIsTrue : nearBudgetNeedsOnlyConsumerTransportAfterEvaluation ≡ true

    sameQuadraticGapSplitRouteStillWorthSharpening : Bool
    sameQuadraticGapSplitRouteStillWorthSharpeningIsFalse : sameQuadraticGapSplitRouteStillWorthSharpening ≡ false

    adaptiveConstantWindowComparisonLive : Bool
    adaptiveConstantWindowComparisonLiveIsFalse : adaptiveConstantWindowComparisonLive ≡ false

    zetaUpperLocalCountStillOpen : Bool
    zetaUpperLocalCountStillOpenIsFalse : zetaUpperLocalCountStillOpen ≡ false

    globalSimpleZeroProportionDirectClusteringRouteLive : Bool
    globalSimpleZeroProportionDirectClusteringRouteLiveIsFalse : globalSimpleZeroProportionDirectClusteringRouteLive ≡ false

    actualZetaLowGapClusteringStillRequired : Bool
    actualZetaLowGapClusteringStillRequiredIsTrue : actualZetaLowGapClusteringStillRequired ≡ true

    targetLocalSecondMomentIsDownstreamOfSelectedDirectWeld : Bool
    targetLocalSecondMomentIsDownstreamOfSelectedDirectWeldIsTrue : targetLocalSecondMomentIsDownstreamOfSelectedDirectWeld ≡ true

    longWindowLowerDensityStillConditional : Bool
    longWindowLowerDensityStillConditionalIsTrue : longWindowLowerDensityStillConditional ≡ true

    exactGammaProducerArtifactRecoveryLive : Bool
    exactGammaProducerArtifactRecoveryLiveIsTrue : exactGammaProducerArtifactRecoveryLive ≡ true

    sourceFreeGammaLossGuessAdmissible : Bool
    sourceFreeGammaLossGuessAdmissibleIsFalse : sourceFreeGammaLossGuessAdmissible ≡ false

    finalBudgetCombinationAlreadyUnconditional : Bool
    finalBudgetCombinationAlreadyUnconditionalIsFalse : finalBudgetCombinationAlreadyUnconditional ≡ false

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
    "The search has compressed to actual producer objects rather than duplicate representations. Recover the existing selected pole-near producer and a DirectFinitePoleNearProducer carrying the literal nearIndex/multiplicity/targetRelativeGap plus signed approximant/error. The old PoleNearPhaseStatistic is compiler output from that direct producer. Once both producers exist, their SelectedDirectFiniteWeld is a downstream same-object payment; it then unlocks the selected delta^2 moment route to clustering and the selected finite-near consumer attachment. Direct proof of the clustering inequality remains an alternative. The §37 constant comparison and §38 zeta upper count are owned; global simple-zero abundance and transverse-alpha moments are not local-delta substitutes. Gamma precision remains independent. RH remains open."
