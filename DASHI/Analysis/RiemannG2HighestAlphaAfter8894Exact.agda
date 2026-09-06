module DASHI.Analysis.RiemannG2HighestAlphaAfter8894Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2GapSplitClusteringLeanReturn8894Exact as Gap
import DASHI.Analysis.RiemannAristotleQuarterPeriodDensityWindowLeanReturnExact as Q37
import DASHI.Analysis.RiemannAristotleZetaLocalCountLeanReturnExact as Z38
import DASHI.Analysis.RiemannAristotlePoleQuotientDirectFiniteNearAttackExact as Direct
import DASHI.Analysis.RiemannG2TargetCenteredScalarCancellationAssemblyExact as Literal
import DASHI.Analysis.RiemannG2SelectedDirectFiniteMomentBidiExact as Shared
import DASHI.Analysis.RiemannAristotlePoleNearPhaseStatisticExact as Phase
import DASHI.Analysis.RiemannG2SelectedPoleNearFiniteEvaluationSameObjectExact as NearEval
import DASHI.Analysis.RiemannG2GammaProducerSourceAcquisitionExact as GammaSource
import DASHI.Analysis.RiemannG2PoleQuotientProducerReconciliation8889Exact as PQ

------------------------------------------------------------------------
-- HIGHEST-ALPHA SCHEDULER AFTER 8894 / 8896 — CORRECTED DIRECTION
--
-- §35's clustering inequality is a NECESSARY condition for positivity of the
-- gap-split lower-bound obstruction. It is not a forward RH producer. §37/§38
-- close two obstruction-audit coordinates (J*Lambda compatibility and zeta
-- upper local count) without changing the actual G2d forward target.
--
-- The direct owner now makes that target exact:
--
--   DirectSignedConsumerPayment P
--     = AcceptableForG2Consumer P (totalSignedResponse P).
--
-- A recovered DirectFinitePoleNearProducer must carry this payment and therefore
-- closes the existing literal G2d scalar consumer. Its carrier fields compile
-- from the canonical LiteralTargetCenteredScalarProblem. Selected-window weld,
-- budget transport, and any literal M2_delta/clustering audit are downstream.
--
-- Gamma precision remains an independent live branch.
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
  pruned owned live conditional downstream diagnostic : LeafState

leafState : RH8894Leaf -> LeafState
leafState searchForModulationOperation = owned
leafState rebuildCharacterMultiplication = pruned
leafState identifyWholeSourceFunctionSpaceWithWeilTest = pruned
leafState identifyWholeSourceFunctionSpaceWithMellinTest = pruned
leafState separatelyRecoverSelectedFkOrbitAttachment = pruned
leafState separatelyRecoverSelectedNearFarWeld = pruned
leafState separatelyRecoverSelectedSameTestWeld = pruned
leafState recoverActualSelectedPoleNearProducer = downstream

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
leafState proveActualZetaLowGapClustering = diagnostic
leafState proveTargetLocalSecondMoment = diagnostic
leafState supplyZetaLongWindowLowerDensity = diagnostic

leafState searchForAnyGammaBound = pruned
leafState guessGammaLossWithoutSource = pruned
leafState recoverExactGammaProducerArtifact = live
leafState recoverExactGammaProducerDecomposition = live
leafState localizeGammaPrecisionLossOnRecoveredProducer = downstream
leafState repairGammaToSharpWindow = downstream
leafState attachOwnedClusterMargin = downstream
leafState combineFinalIndependentBudgets = conditional

------------------------------------------------------------------------
-- Key inherited receipts and pruning.
------------------------------------------------------------------------

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

actualZetaClusteringStillUnproved :
  Z38.actualZetaClusteringClosed Z38.canonicalZetaLocalCountLeanReturn ≡ false
actualZetaClusteringStillUnproved = refl

clusteringIsNotForwardRHPayment :
  Gap.clusteringDirectlyPaysRHScalarConsumer
    Gap.canonicalGapSplitClusteringLeanReturn8894 ≡ false
clusteringIsNotForwardRHPayment = Gap.clusteringDoesNotDirectlyPayRH

directProducerMustCarryConsumerPayment :
  Direct.DirectFiniteNearAttackBoundary.directProducerCarriesCanonicalConsumerPayment
    Direct.canonicalDirectFiniteNearAttackBoundary ≡ true
directProducerMustCarryConsumerPayment = refl

genericWithinDoesNotCloseConsumer :
  Direct.DirectFiniteNearAttackBoundary.genericWithinReceiptAloneIsSufficient
    Direct.canonicalDirectFiniteNearAttackBoundary ≡ false
genericWithinDoesNotCloseConsumer = refl

literalDirectAcceptanceCompilerOwned :
  Literal.TargetCenteredScalarCancellationBoundary.directSignedAcceptanceCompilesToExactConsumerReceipt
    Literal.canonicalTargetCenteredScalarCancellationBoundary ≡ true
literalDirectAcceptanceCompilerOwned = refl

secondPhaseStatisticCarrierNoLongerLive :
  Phase.paymentState Phase.constructSecondPhaseStatisticCarrier ≡ Phase.pruned
secondPhaseStatisticCarrierNoLongerLive = Phase.secondPhaseStatisticCarrierPruned

phaseStatisticCompilerOwned :
  Phase.PoleNearPhaseStatisticBoundary.repositoryAlreadyOwnsConcretePoleNearPhaseStatistic
    Phase.canonicalPoleNearPhaseStatisticBoundary ≡ true
phaseStatisticCompilerOwned = refl

selectedDirectWeldIsDownstream :
  Shared.paymentState Shared.weldExistingDirectProducerToSelectedWindow ≡ Shared.downstream
selectedDirectWeldIsDownstream = refl

literalMomentIsDiagnosticDownstream :
  Shared.paymentState Shared.proveLiteralOrdinateMomentBoundAfterWeld ≡ Shared.downstream
literalMomentIsDiagnosticDownstream = refl

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

genericGammaSearchNoLongerLive :
  PQ.LeafRelevant PQ.findAnyGammaUpperBound -> ⊥
genericGammaSearchNoLongerLive = PQ.findAnyGammaUpperBoundPruned

guessGammaStirlingLossNoLongerLive :
  GammaSource.SearchRelevant GammaSource.guessStirlingLossWithoutProducer -> ⊥
guessGammaStirlingLossNoLongerLive = GammaSource.guessStirlingLossWithoutProducerPruned

guessGammaDigammaLossNoLongerLive :
  GammaSource.SearchRelevant GammaSource.guessDigammaLossWithoutProducer -> ⊥
guessGammaDigammaLossNoLongerLive = GammaSource.guessDigammaLossWithoutProducerPruned

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
    literalFkSourceMathematicsAlreadyRecoveredIsTrue :
      literalFkSourceMathematicsAlreadyRecovered ≡ true

    directFinitePoleNearProducerStillRequired : Bool
    directFinitePoleNearProducerStillRequiredIsTrue :
      directFinitePoleNearProducerStillRequired ≡ true

    directProducerCarriesCanonicalConsumerPayment : Bool
    directProducerCarriesCanonicalConsumerPaymentIsTrue :
      directProducerCarriesCanonicalConsumerPayment ≡ true

    finiteNearCarrierAndFarShellFreshMathematicsRequired : Bool
    finiteNearCarrierAndFarShellFreshMathematicsRequiredIsFalse :
      finiteNearCarrierAndFarShellFreshMathematicsRequired ≡ false

    secondPhaseStatisticCarrierRequired : Bool
    secondPhaseStatisticCarrierRequiredIsFalse :
      secondPhaseStatisticCarrierRequired ≡ false

    selectedWindowAndBudgetWorkDownstreamOfDirectProducer : Bool
    selectedWindowAndBudgetWorkDownstreamOfDirectProducerIsTrue :
      selectedWindowAndBudgetWorkDownstreamOfDirectProducer ≡ true

    adaptiveConstantWindowComparisonLive : Bool
    adaptiveConstantWindowComparisonLiveIsFalse :
      adaptiveConstantWindowComparisonLive ≡ false

    zetaUpperLocalCountStillOpen : Bool
    zetaUpperLocalCountStillOpenIsFalse : zetaUpperLocalCountStillOpen ≡ false

    actualZetaClusteringIsForwardRHPayment : Bool
    actualZetaClusteringIsForwardRHPaymentIsFalse :
      actualZetaClusteringIsForwardRHPayment ≡ false

    actualZetaClusteringRetainedAsObstructionDiagnostic : Bool
    actualZetaClusteringRetainedAsObstructionDiagnosticIsTrue :
      actualZetaClusteringRetainedAsObstructionDiagnostic ≡ true

    targetLocalSecondMomentIsForwardRHPayment : Bool
    targetLocalSecondMomentIsForwardRHPaymentIsFalse :
      targetLocalSecondMomentIsForwardRHPayment ≡ false

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
    true refl
    false refl
    false refl
    true refl
    false refl
    false refl
    false refl
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    "After the checked §35-§38 audit, do not confuse an obstruction condition with a forward RH theorem. Low-gap clustering is necessary only for positivity of the gap-split lower-bound no-go; it is not the signed-cancellation payment. The highest-alpha forward zero-side theorem is now explicit: recover DirectSignedConsumerPayment = AcceptableForG2Consumer(totalSignedResponse) on the canonical LiteralTargetCenteredScalarProblem, packaged by DirectFinitePoleNearProducer. Canonical carrier fields, phase statistic and evaluation surface are compiler output. Selected-window/budget transport is downstream. Gamma producer precision remains the independent live branch. RH remains open."
