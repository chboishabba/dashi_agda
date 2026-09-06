module DASHI.Analysis.RiemannAristotleNearCoreDensityReturnRegression where

open import DASHI.Core.Prelude
import DASHI.Analysis.RiemannAristotleQuarterPeriodDensityWindowLeanReturnExact as Q
import DASHI.Analysis.RiemannAristotleZetaLocalCountLeanReturnExact as Z
import DASHI.Analysis.RiemannG2GapSplitClusteringLeanReturn8894Exact as Gap
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

actualClusteringOpen :
  Z.ZetaLocalCountLeanReturn.actualZetaClusteringClosed
    Z.canonicalZetaLocalCountLeanReturn ≡ false
actualClusteringOpen = refl

-- BIDI propagation: the old 8894 owner itself now routes to clustering.
gapSplitRouteNowClustering :
  Gap.currentGapSplitRouteState ≡ Gap.clusteringRequired
gapSplitRouteNowClustering = refl

quarterDensitySearchLeafPruned :
  Gap.GapSplitRelevant
    Gap.compareQuarterPeriodLowerConstantWithDensityUpperConstant → ⊥
quarterDensitySearchLeafPruned = Gap.quarterDensityConstantComparisonPruned

zetaUpperCountSearchLeafPruned :
  Gap.GapSplitRelevant Gap.recoverZetaUpperLocalCount → ⊥
zetaUpperCountSearchLeafPruned = Gap.zetaUpperLocalCountSearchPruned

-- The former parallel width/crossing work package is closed in place.
widthAndCrossingPackageClosed :
  Quarter.workState Quarter.widthAndCrossingScale ≡ Quarter.closed
widthAndCrossingPackageClosed = refl

quarterSchedulerRoutesToClustering :
  Quarter.workState Quarter.actualZetaLowGapClustering ≡ Quarter.live
quarterSchedulerRoutesToClustering = refl

-- Canonical root scheduler now sees the new zero-spacing producer.
rootSchedulerClusteringActive :
  Root.RHBidiSearchSchedulerBoundary.actualZetaLowGapClusteringActive
    Root.canonicalRHBidiSearchSchedulerBoundary ≡ true
rootSchedulerClusteringActive = refl

rootSchedulerZetaUpperCountNotActive :
  Root.RHBidiSearchSchedulerBoundary.zetaUpperCountRemainsInActiveQueue
    Root.canonicalRHBidiSearchSchedulerBoundary ≡ false
rootSchedulerZetaUpperCountNotActive = refl

rootSchedulerQuarterDensityNotActive :
  Root.RHBidiSearchSchedulerBoundary.quarterDensityConstantComparisonRemainsInActiveQueue
    Root.canonicalRHBidiSearchSchedulerBoundary ≡ false
rootSchedulerQuarterDensityNotActive = refl

-- Canonical analytic-leaf scheduler exposes clustering as a real schedulable leaf.
analyticLeafClusteringOpen :
  Leaf.leafState Leaf.proveActualZetaLowGapClustering ≡ Leaf.open
analyticLeafClusteringOpen = refl

analyticLeafClusteringSchedulable :
  Leaf.RHAnalyticLeafSchedulable Leaf.proveActualZetaLowGapClustering
analyticLeafClusteringSchedulable = Leaf.zetaLowGapClusteringLeafLive

rhStillOpen :
  Z.ZetaLocalCountLeanReturn.rhDerived
    Z.canonicalZetaLocalCountLeanReturn ≡ false
rhStillOpen = refl
