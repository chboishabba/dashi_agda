module DASHI.Biology.Agriculture.QueenslandLegumeResidueFallowRecoveryRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.QueenslandLegumeResidueFallowRecoveryExact as R

publicationDatePinned :
  R.grdcPublicationDate ≡ "2026-03-03"
publicationDatePinned = refl

shortFallowMonthsPinned :
  R.fallowMonths R.shortFallowBarleyReceipt ≡ 2
shortFallowMonthsPinned = refl

longFallowMonthsPinned :
  R.fallowMonths R.longFallowSorghumReceipt ≡ 9
longFallowMonthsPinned = refl

barleyFertiliserPinned :
  R.followingCropFertiliserNkgHa R.shortFallowBarleyReceipt ≡ 50
barleyFertiliserPinned = refl

sorghumFertiliserPinned :
  R.followingCropFertiliserNkgHa R.longFallowSorghumReceipt ≡ 0
sorghumFertiliserPinned = refl

shortAGNdfrLowerPinned :
  R.agNdfrLowerKgHa R.shortFallowBarleyReceipt ≡ 11
shortAGNdfrLowerPinned = refl

shortAGCombinedUpperPinned :
  R.agBgNdfrUpperKgHa R.shortFallowBarleyReceipt ≡ 25
shortAGCombinedUpperPinned = refl

longAGNdfrLowerPinned :
  R.agNdfrLowerKgHa R.longFallowSorghumReceipt ≡ 9
longAGNdfrLowerPinned = refl

longCombinedUpperPinned :
  R.agBgNdfrUpperKgHa R.longFallowSorghumReceipt ≡ 16
longCombinedUpperPinned = refl

routeTimeRecoveryJoinOwned :
  R.sameExperimentRouteFallowRecoveryJoinOwned
    R.canonicalFallowRecoveryBoundary ≡ true
routeTimeRecoveryJoinOwned = refl

bgRecoveryDenominatorNotDirectMeasurement :
  R.bgRecoveryEfficiencyDenominatorDirectlyMeasured
    R.canonicalFallowRecoveryBoundary ≡ false
bgRecoveryDenominatorNotDirectMeasurement = refl

barleyRecoveryNotFertiliserReplacement :
  R.shortFallowRecoveryEqualsAvoidedMineralFertiliser
    R.canonicalFallowRecoveryBoundary ≡ false
barleyRecoveryNotFertiliserReplacement = refl

notAcaciaSameObject :
  R.queenslandCroppingResidueRecoveryCreatesAcaciaSameObjectEvidence
    R.canonicalFallowRecoveryBoundary ≡ false
notAcaciaSameObject = refl
