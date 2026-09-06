module DASHI.Analysis.RiemannAristotleNearCoreDensityReturnRegression where

open import DASHI.Core.Prelude
import DASHI.Analysis.RiemannAristotleQuarterPeriodDensityWindowLeanReturnExact as Q
import DASHI.Analysis.RiemannAristotleZetaLocalCountLeanReturnExact as Z

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

rhStillOpen :
  Z.ZetaLocalCountLeanReturn.rhDerived
    Z.canonicalZetaLocalCountLeanReturn ≡ false
rhStillOpen = refl
