module DASHI.Analysis.RiemannAristotleNearCoreDensityReturnRegression where

open import DASHI.Core.Prelude
import DASHI.Analysis.RiemannAristotleQuarterPeriodDensityWindowLeanReturnExact as Q
import DASHI.Analysis.RiemannAristotleZetaLocalCountLeanReturnExact as Z
import DASHI.Analysis.RiemannG2GapSplitClusteringLeanReturn8894Exact as Gap
import DASHI.Analysis.RiemannG2AlpogeFurmanClusteringNonDescentExact as AFLocal
import DASHI.Analysis.RiemannG2LowGapClusteringMomentReductionExact as Moment
import DASHI.Analysis.RiemannG2SelectedTargetLocalMomentSameObjectExact as SelectedMoment
import DASHI.Analysis.RiemannG2SelectedDirectFiniteMomentBidiExact as Shared
import DASHI.Analysis.RiemannAristotlePoleNearPhaseStatisticExact as Phase
import DASHI.Analysis.RiemannAristotlePoleQuotientDirectFiniteNearAttackExact as Direct
import DASHI.Analysis.RiemannG2TargetCenteredScalarCancellationAssemblyExact as Literal
import DASHI.Analysis.RiemannG2QuarterPeriodAnalyticRouteReconciliationExact as Quarter
import DASHI.Analysis.RiemannAristotleRHBidiSearchSchedulerExact as Root
import DASHI.Analysis.RiemannAristotleRHAnalyticLeafSchedulerExact as Leaf

quarterDensityCheckedInLean :
  Q.QuarterPeriodDensityWindowReturn.machineCheckedInLean
    Q.canonicalQuarterPeriodDensityWindowReturn ≡ true
quarterDensityCheckedInLean = refl

quarterDensityNotPromotedToAgda :
  Q.QuarterPeriodDensityWindowReturn.transportedIntoAgda
    Q.canonicalQuarterPeriodDensityWindowReturn ≡ false
quarterDensityNotPromotedToAgda = refl

inverseWidthNoGoRejected :
  Q.QuarterPeriodDensityWindowReturn.densityCutRefutesInverseWidthRoute
    Q.canonicalQuarterPeriodDensityWindowReturn ≡ false
inverseWidthNoGoRejected = refl

matchedAsymptoticNotPromoted :
  Q.QuarterPeriodDensityWindowReturn.matchedDensityAsymptoticProvedBySection37
    Q.canonicalQuarterPeriodDensityWindowReturn ≡ false
matchedAsymptoticNotPromoted = refl

zetaProducerChecked :
  Z.ZetaLocalCountLeanReturn.importedProducerCheckedInLean
    Z.canonicalZetaLocalCountLeanReturn ≡ true
zetaProducerChecked = refl

zetaProducerNotAuthorityReceipt :
  Z.ZetaLocalCountLeanReturn.importedProducerIsUnprovedAuthorityReceipt
    Z.canonicalZetaLocalCountLeanReturn ≡ false
zetaProducerNotAuthorityReceipt = refl

zetaProducerNotAgdaProof :
  Z.ZetaLocalCountLeanReturn.transportedIntoAgda
    Z.canonicalZetaLocalCountLeanReturn ≡ false
zetaProducerNotAgdaProof = refl

zetaUpperCountingClosed :
  Z.ZetaLocalCountLeanReturn.zetaUpperCountingHypothesisStillOpen
    Z.canonicalZetaLocalCountLeanReturn ≡ false
zetaUpperCountingClosed = refl

longWindowLowerDensityOpen :
  Z.ZetaLocalCountLeanReturn.zetaLongWindowLowerDensityClosed
    Z.canonicalZetaLocalCountLeanReturn ≡ false
longWindowLowerDensityOpen = refl

actualClusteringUnproved :
  Z.ZetaLocalCountLeanReturn.actualZetaClusteringClosed
    Z.canonicalZetaLocalCountLeanReturn ≡ false
actualClusteringUnproved = refl

------------------------------------------------------------------------
-- Gap-split semantics: clusteringRequired is an obstruction-state name, NOT a
-- forward RH producer classification.
------------------------------------------------------------------------

gapSplitRouteStillNamesClusteringObstruction :
  Gap.currentGapSplitRouteState ≡ Gap.clusteringRequired
gapSplitRouteStillNamesClusteringObstruction = refl

gapSplitClusteringIsObstructionDiagnostic :
  Gap.clusteringConditionIsGapSplitObstructionDiagnostic
    Gap.canonicalGapSplitClusteringLeanReturn8894 ≡ true
gapSplitClusteringIsObstructionDiagnostic = refl

gapSplitClusteringDoesNotPayRH :
  Gap.clusteringDirectlyPaysRHScalarConsumer
    Gap.canonicalGapSplitClusteringLeanReturn8894 ≡ false
gapSplitClusteringDoesNotPayRH = Gap.clusteringDoesNotDirectlyPayRH

quarterDensitySearchLeafPruned :
  Gap.GapSplitRelevant Gap.compareQuarterPeriodLowerConstantWithDensityUpperConstant → ⊥
quarterDensitySearchLeafPruned = Gap.quarterDensityConstantComparisonPruned

zetaUpperCountSearchLeafPruned :
  Gap.GapSplitRelevant Gap.recoverZetaUpperLocalCount → ⊥
zetaUpperCountSearchLeafPruned = Gap.zetaUpperLocalCountSearchPruned

------------------------------------------------------------------------
-- Donor diagnostics remain valid but do not create RH producers.
------------------------------------------------------------------------

alpogeFurmanGlobalViewsCollide :
  AFLocal.globalSimpleView AFLocal.sameGlobalClustered ≡
  AFLocal.globalSimpleView AFLocal.sameGlobalUnclustered
alpogeFurmanGlobalViewsCollide = AFLocal.sameGlobalSummary

alpogeFurmanLocalViewsSeparate :
  AFLocal.localGapView AFLocal.sameGlobalClustered ≡
  AFLocal.localGapView AFLocal.sameGlobalUnclustered → ⊥
alpogeFurmanLocalViewsSeparate = AFLocal.localPatternsDiffer

alpogeFurmanDirectClusteringPruned :
  AFLocal.GlobalSimpleToLocalClusteringBoundary.alpogeFurmanDirectlyClosesGapSplitClustering
    AFLocal.canonicalGlobalSimpleToLocalClusteringBoundary ≡ false
alpogeFurmanDirectClusteringPruned = refl

localMomentRatioCompilerClosed :
  Moment.LocalMomentClusteringBoundary.natMomentToTwoToOneRatioCompilerClosedInAgda
    Moment.canonicalLocalMomentClusteringBoundary ≡ true
localMomentRatioCompilerClosed = refl

selectedTargetLocalMomentUnproved :
  Moment.LocalMomentClusteringBoundary.exactSelectedTargetLocalSecondMomentProducerOwned
    Moment.canonicalLocalMomentClusteringBoundary ≡ false
selectedTargetLocalMomentUnproved = refl

selectedMomentExactConsumerShape :
  SelectedMoment.SelectedTargetLocalMomentBoundary.selectedWindowMomentAttachmentIsExactConsumerShape
    SelectedMoment.canonicalSelectedTargetLocalMomentBoundary ≡ true
selectedMomentExactConsumerShape = refl

selectedDirectWeldProofBearing :
  Shared.SelectedDirectFiniteMomentBoundary.selectedDirectWeldClaimsAreProofBearing
    Shared.canonicalSelectedDirectFiniteMomentBoundary ≡ true
selectedDirectWeldProofBearing = refl

momentNormalizationProofBearing :
  Shared.SelectedDirectFiniteMomentBoundary.momentNormalizationClaimsAreProofBearing
    Shared.canonicalSelectedDirectFiniteMomentBoundary ≡ true
momentNormalizationProofBearing = refl

secondMomentDefinitionPruned :
  Shared.paymentState Shared.constructSecondMomentDefinition ≡ Shared.pruned
secondMomentDefinitionPruned = Shared.secondMomentDefinitionPruned

------------------------------------------------------------------------
-- Direct literal producer is the forward zero-side leaf.
------------------------------------------------------------------------

directProducerCarriesCanonicalConsumerPayment :
  Direct.DirectFiniteNearAttackBoundary.directProducerCarriesCanonicalConsumerPayment
    Direct.canonicalDirectFiniteNearAttackBoundary ≡ true
directProducerCarriesCanonicalConsumerPayment = refl

genericWithinAloneInsufficient :
  Direct.DirectFiniteNearAttackBoundary.genericWithinReceiptAloneIsSufficient
    Direct.canonicalDirectFiniteNearAttackBoundary ≡ false
genericWithinAloneInsufficient = refl

literalAcceptanceCompilerClosed :
  Literal.TargetCenteredScalarCancellationBoundary.directSignedAcceptanceCompilesToExactConsumerReceipt
    Literal.canonicalTargetCenteredScalarCancellationBoundary ≡ true
literalAcceptanceCompilerClosed = refl

concretePhaseStatisticNowOwned :
  Phase.PoleNearPhaseStatisticBoundary.repositoryAlreadyOwnsConcretePoleNearPhaseStatistic
    Phase.canonicalPoleNearPhaseStatisticBoundary ≡ true
concretePhaseStatisticNowOwned = refl

secondPhaseCarrierPruned :
  Phase.paymentState Phase.constructSecondPhaseStatisticCarrier ≡ Phase.pruned
secondPhaseCarrierPruned = Phase.secondPhaseStatisticCarrierPruned

------------------------------------------------------------------------
-- Quarter-period scheduler: compatibility closed, clustering diagnostic,
-- literal direct signed producer forward-live.
------------------------------------------------------------------------

widthAndCrossingPackageClosed :
  Quarter.workState Quarter.widthAndCrossingScale ≡ Quarter.closed
widthAndCrossingPackageClosed = refl

quarterClusteringIsDiagnostic :
  Quarter.workState Quarter.actualZetaLowGapClustering ≡ Quarter.diagnostic
quarterClusteringIsDiagnostic = Quarter.actualZetaClusteringIsDiagnostic

quarterLiteralDirectProducerLive :
  Quarter.workState Quarter.literalDirectSignedProducer ≡ Quarter.live
quarterLiteralDirectProducerLive = Quarter.literalDirectSignedProducerIsLive

------------------------------------------------------------------------
-- Canonical root scheduler rejects clustering/moment as RH leaves.
------------------------------------------------------------------------

rootSchedulerClusteringInactive :
  Root.RHBidiSearchSchedulerBoundary.actualZetaLowGapClusteringActive
    Root.canonicalRHBidiSearchSchedulerBoundary ≡ false
rootSchedulerClusteringInactive = refl

rootSchedulerClusteringDiagnostic :
  Root.RHBidiSearchSchedulerBoundary.clusteringRetainedAsObstructionDiagnostic
    Root.canonicalRHBidiSearchSchedulerBoundary ≡ true
rootSchedulerClusteringDiagnostic = refl

rootSchedulerDirectProducerActive :
  Root.RHBidiSearchSchedulerBoundary.directFinitePoleNearProducerActive
    Root.canonicalRHBidiSearchSchedulerBoundary ≡ true
rootSchedulerDirectProducerActive = refl

rootSchedulerDirectProducerCarriesPayment :
  Root.RHBidiSearchSchedulerBoundary.directProducerCarriesCanonicalSignedConsumerPayment
    Root.canonicalRHBidiSearchSchedulerBoundary ≡ true
rootSchedulerDirectProducerCarriesPayment = refl

rootSchedulerSelectedWeldDownstream :
  Root.RHBidiSearchSchedulerBoundary.selectedDirectZeroCarrierWeldActive
    Root.canonicalRHBidiSearchSchedulerBoundary ≡ false
rootSchedulerSelectedWeldDownstream = refl

rootSchedulerMomentNotForwardActive :
  Root.RHBidiSearchSchedulerBoundary.targetLocalSecondMomentRefinementActive
    Root.canonicalRHBidiSearchSchedulerBoundary ≡ false
rootSchedulerMomentNotForwardActive = refl

rootSchedulerMomentStillUsesSelectedWindow :
  Root.RHBidiSearchSchedulerBoundary.targetLocalSecondMomentUsesExistingSelectedWindow
    Root.canonicalRHBidiSearchSchedulerBoundary ≡ true
rootSchedulerMomentStillUsesSelectedWindow = refl

rootSchedulerZetaUpperCountNotActive :
  Root.RHBidiSearchSchedulerBoundary.zetaUpperCountRemainsInActiveQueue
    Root.canonicalRHBidiSearchSchedulerBoundary ≡ false
rootSchedulerZetaUpperCountNotActive = refl

rootSchedulerQuarterDensityNotActive :
  Root.RHBidiSearchSchedulerBoundary.quarterDensityConstantComparisonRemainsInActiveQueue
    Root.canonicalRHBidiSearchSchedulerBoundary ≡ false
rootSchedulerQuarterDensityNotActive = refl

rootClusteringExperimentNotSchedulable :
  Root.RHBidiSchedulable Root.proveActualZetaLowGapClustering → ⊥
rootClusteringExperimentNotSchedulable = Root.zetaClusteringNotSchedulableAsRHProducer

rootDirectExperimentSchedulable :
  Root.RHBidiSchedulable Root.recoverDirectFinitePoleNearProducer
rootDirectExperimentSchedulable = Root.directFinitePoleNearProducerSchedulable

------------------------------------------------------------------------
-- Analytic-leaf scheduler agrees.
------------------------------------------------------------------------

analyticLeafClusteringPrunedFromRHQueue :
  Leaf.leafState Leaf.proveActualZetaLowGapClustering ≡ Leaf.pruned
analyticLeafClusteringPrunedFromRHQueue = refl

analyticLeafClusteringNotSchedulable :
  Leaf.RHAnalyticLeafSchedulable Leaf.proveActualZetaLowGapClustering → ⊥
analyticLeafClusteringNotSchedulable = Leaf.zetaClusteringDiagnosticNotRHSchedulable

analyticLeafMomentPrunedFromRHQueue :
  Leaf.leafState Leaf.proveSelectedTargetLocalSecondMoment ≡ Leaf.pruned
analyticLeafMomentPrunedFromRHQueue = refl

analyticLeafDirectProducerSchedulable :
  Leaf.RHAnalyticLeafSchedulable Leaf.recoverDirectFinitePoleNearProducer
analyticLeafDirectProducerSchedulable = Leaf.directFiniteProducerLeafLive

rhStillOpen :
  Z.ZetaLocalCountLeanReturn.rhDerived
    Z.canonicalZetaLocalCountLeanReturn ≡ false
rhStillOpen = refl
