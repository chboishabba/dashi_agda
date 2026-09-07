module DASHI.Analysis.RiemannAristotleCurrentFrontierRegression where

open import DASHI.Core.Prelude
import DASHI.Analysis.RiemannAristotleCurrentFrontierExact as F

evenConeClosed :
  F.AristotleCurrentFrontier.universalEvenConeConstructionClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
evenConeClosed = refl

twoRadiusClosed :
  F.AristotleCurrentFrontier.twoRadiusOffLineDiscriminatorClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
twoRadiusClosed = refl

primeZero :
  F.AristotleCurrentFrontier.highOrdinatePrimeProjectiveDebtZeroInLean
    F.canonicalAristotleCurrentFrontier ≡ true
primeZero = refl

deterministicSchurKernelChecked :
  F.AristotleCurrentFrontier.deterministicProjectiveSchurKernelCheckedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
deterministicSchurKernelChecked = refl

explicitFarCutoffClosed :
  F.AristotleCurrentFrontier.explicitFarShellCutoffBoundClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
explicitFarCutoffClosed = refl

explicitFarDecayClosed :
  F.AristotleCurrentFrontier.explicitFarShellTendsToZeroClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
explicitFarDecayClosed = refl

finiteNearCarrierClosed :
  F.AristotleCurrentFrontier.finiteSignedNearCarrierClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
finiteNearCarrierClosed = refl

literalDoffCutoffClosed :
  F.AristotleCurrentFrontier.literalDoffCutoffCarrierClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
literalDoffCutoffClosed = refl

latestLeanBuildChecked :
  F.AristotleCurrentFrontier.latestLeanBridgeBuildKernelChecked
    F.canonicalAristotleCurrentFrontier ≡ true
latestLeanBuildChecked = refl

quarterDensityReconciled :
  F.AristotleCurrentFrontier.quarterPeriodDensityReconciliationClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
quarterDensityReconciled = refl

zetaUnitCountClosed :
  F.AristotleCurrentFrontier.zetaUnitLocalCountClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
zetaUnitCountClosed = refl

zetaShortWindowCountClosed :
  F.AristotleCurrentFrontier.zetaShortWindowUpperCountClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
zetaShortWindowCountClosed = refl

densityCutDoesNotKillInverseWidth :
  F.AristotleCurrentFrontier.densityCutRefutesInverseWidthRoute
    F.canonicalAristotleCurrentFrontier ≡ false
densityCutDoesNotKillInverseWidth = refl

zetaLongWindowLowerDensityOpen :
  F.AristotleCurrentFrontier.zetaLongWindowLowerDensityClosed
    F.canonicalAristotleCurrentFrontier ≡ false
zetaLongWindowLowerDensityOpen = refl

zetaClusteringUnproved :
  F.AristotleCurrentFrontier.actualZetaClusteringClosed
    F.canonicalAristotleCurrentFrontier ≡ false
zetaClusteringUnproved = refl

zetaClusteringNotForwardRHProducer :
  F.actualZetaClusteringIsForwardRHProducer ≡ false
zetaClusteringNotForwardRHProducer =
  F.actualZetaClusteringIsForwardRHProducerIsFalse

zetaClusteringIsGapSplitDiagnostic :
  F.actualZetaClusteringIsGapSplitObstructionDiagnostic ≡ true
zetaClusteringIsGapSplitDiagnostic =
  F.actualZetaClusteringIsGapSplitObstructionDiagnosticIsTrue

localMomentCompilerClosed :
  F.AristotleCurrentFrontier.targetLocalSecondMomentCompilerClosedInAgda
    F.canonicalAristotleCurrentFrontier ≡ true
localMomentCompilerClosed = refl

localMomentProducerUnproved :
  F.AristotleCurrentFrontier.targetLocalSecondMomentProducerClosed
    F.canonicalAristotleCurrentFrontier ≡ false
localMomentProducerUnproved = refl

localMomentUsesSelectedWindow :
  F.AristotleCurrentFrontier.targetLocalMomentUsesExistingSelectedWindow
    F.canonicalAristotleCurrentFrontier ≡ true
localMomentUsesSelectedWindow = refl

localMomentNotForwardRHProducer :
  F.targetLocalSecondMomentIsForwardRHProducer ≡ false
localMomentNotForwardRHProducer =
  F.targetLocalSecondMomentIsForwardRHProducerIsFalse

phaseStatisticCompilerClosed :
  F.AristotleCurrentFrontier.concretePhaseStatisticCompilerClosedInAgda
    F.canonicalAristotleCurrentFrontier ≡ true
phaseStatisticCompilerClosed = refl

selectedDirectWeldOpen :
  F.AristotleCurrentFrontier.selectedDirectZeroCarrierWeldClosed
    F.canonicalAristotleCurrentFrontier ≡ false
selectedDirectWeldOpen = refl

sharedDirectCarrierFeedsBothDiagnosticAndFiniteNear :
  F.AristotleCurrentFrontier.oneDirectGapCarrierFeedsClusteringAndFiniteNear
    F.canonicalAristotleCurrentFrontier ≡ true
sharedDirectCarrierFeedsBothDiagnosticAndFiniteNear = refl

transverseMomentNotOrdinateClustering :
  F.AristotleCurrentFrontier.transverseMomentDirectlyControlsOrdinateClustering
    F.canonicalAristotleCurrentFrontier ≡ false
transverseMomentNotOrdinateClustering = refl

alpogeFurmanNotDirectLocalClosure :
  F.AristotleCurrentFrontier.alpogeFurmanGlobalSimpleProportionDirectlyClosesClustering
    F.canonicalAristotleCurrentFrontier ≡ false
alpogeFurmanNotDirectLocalClosure = refl

-- Determinant compiler remains useful internally, but is not the final carrier.
directPaymentCompilerClosed :
  F.directSignedConsumerPaymentCompilerClosedInAgda ≡ true
directPaymentCompilerClosed =
  F.directSignedConsumerPaymentCompilerClosedInAgdaIsTrue

literalDirectProducerStillOpen :
  F.literalDirectFiniteProducerClosed ≡ false
literalDirectProducerStillOpen = F.literalDirectFiniteProducerClosedIsFalse

genericWithinDoesNotCloseLiteralG2 :
  F.genericWithinReceiptAloneClosesLiteralG2 ≡ false
genericWithinDoesNotCloseLiteralG2 =
  F.genericWithinReceiptAloneClosesLiteralG2IsFalse

-- Final pole-quotient precedence must not regress.
determinantNotFinalCarrier :
  F.FinalCut.PoleQuotientFinalCutBoundary.determinantLaneIsFinalPoleQuotientCarrier
    F.FinalCut.canonicalPoleQuotientFinalCutBoundary ≡ false
determinantNotFinalCarrier = F.determinantLaneIsNotFinalPoleQuotientCarrier

determinantPaymentNotFinalOffPayment :
  F.FinalCut.PoleQuotientFinalCutBoundary.determinantDirectPaymentAutomaticallyPaysFinalOffSocket
    F.FinalCut.canonicalPoleQuotientFinalCutBoundary ≡ false
determinantPaymentNotFinalOffPayment = F.determinantPaymentDoesNotAutoPayFinalOffSocket

universalPoleQuotientOffForward :
  F.FinalCut.PoleQuotientFinalCutBoundary.literalUniversalPoleQuotientSignedOffIsForwardLeaf
    F.FinalCut.canonicalPoleQuotientFinalCutBoundary ≡ true
universalPoleQuotientOffForward = F.universalPoleQuotientSignedOffIsForwardLeaf

gammaPrecisionForward :
  F.FinalCut.PoleQuotientFinalCutBoundary.sameTaperGammaPrecisionIsForwardLeaf
    F.FinalCut.canonicalPoleQuotientFinalCutBoundary ≡ true
gammaPrecisionForward = F.sameTaperGammaPrecisionIsForwardLeaf

clusterFreshAnalysisPruned :
  F.FinalCut.PoleQuotientFinalCutBoundary.freshClusterMarginAnalysisRequired
    F.FinalCut.canonicalPoleQuotientFinalCutBoundary ≡ false
clusterFreshAnalysisPruned = F.freshClusterMarginAnalysisNotRequired

finalCompilerRebuildPruned :
  F.FinalCut.PoleQuotientFinalCutBoundary.finalContradictionCompilerNeedsRebuilding
    F.FinalCut.canonicalPoleQuotientFinalCutBoundary ≡ false
finalCompilerRebuildPruned = F.finalContradictionCompilerRebuildNotRequired

nearFarCompilerClosed :
  F.AristotleCurrentFrontier.nearFarShellCompositionCompilerClosedInAgda
    F.canonicalAristotleCurrentFrontier ≡ true
nearFarCompilerClosed = refl

allowanceCompilerClosed :
  F.AristotleCurrentFrontier.nearFarAllowanceCompilerClosedInAgda
    F.canonicalAristotleCurrentFrontier ≡ true
allowanceCompilerClosed = refl

finiteSchurPerturbationCompilerClosed :
  F.AristotleCurrentFrontier.finiteNearCoreSchurPerturbationCompilerClosedInAgda
    F.canonicalAristotleCurrentFrontier ≡ true
finiteSchurPerturbationCompilerClosed = refl

leanFormulaNotPromotedToAgdaProof :
  F.AristotleCurrentFrontier.explicitLeanTailFormulaTransportedAsAgdaProof
    F.canonicalAristotleCurrentFrontier ≡ false
leanFormulaNotPromotedToAgdaProof = refl

finiteNearSchurCancellationOpen :
  F.AristotleCurrentFrontier.finiteSignedNearSchurCancellationClosed
    F.canonicalAristotleCurrentFrontier ≡ false
finiteNearSchurCancellationOpen = refl

jointFiniteMarginOpen :
  F.AristotleCurrentFrontier.jointFiniteNearFarMarginClosed
    F.canonicalAristotleCurrentFrontier ≡ false
jointFiniteMarginOpen = refl

threeTaperConstructionOpen :
  F.AristotleCurrentFrontier.deterministicNuisanceThreeTaperConstructionClosed
    F.canonicalAristotleCurrentFrontier ≡ false
threeTaperConstructionOpen = refl

lowOrdinateOpen :
  F.AristotleCurrentFrontier.lowOrdinateComplementCertified
    F.canonicalAristotleCurrentFrontier ≡ false
lowOrdinateOpen = refl

rhOpen :
  F.AristotleCurrentFrontier.finalRHImplicationClosed
    F.canonicalAristotleCurrentFrontier ≡ false
rhOpen = refl
