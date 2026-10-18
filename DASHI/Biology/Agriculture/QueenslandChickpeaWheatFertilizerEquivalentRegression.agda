module DASHI.Biology.Agriculture.QueenslandChickpeaWheatFertilizerEquivalentRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.QueenslandChickpeaWheatFertilizerEquivalentExact as Q

doiPinned :
  Q.dalalEtAl1998DOI ≡ "10.1071/EA98027"
doiPinned = refl

meanEquivalentTenthsPinned :
  Q.meanUsableSeasonFertilizerEquivalentTenthsKgHa
    Q.warraChickpeaFertilizerEquivalentReceipt ≡ 492
meanEquivalentTenthsPinned = refl

meanEquivalentSETenthsPinned :
  Q.meanUsableSeasonFertilizerEquivalentSETenthsKgHa
    Q.warraChickpeaFertilizerEquivalentReceipt ≡ 64
meanEquivalentSETenthsPinned = refl

multiRateResponseCurveOwned :
  Q.explicitMultiRateFertilizerResponseCurveOwned
    Q.canonicalChickpeaEquivalentBoundary ≡ true
multiRateResponseCurveOwned = refl

seasonEstimabilityRetained :
  Q.fertilizerEquivalentRequiresInformativeSeasonalResponse
    Q.canonicalChickpeaEquivalentBoundary ≡ true
seasonEstimabilityRetained = refl

dryYearsNotForced :
  Q.nonEstimableDryYearsAssignedReplacementValue
    Q.canonicalChickpeaEquivalentBoundary ≡ false
dryYearsNotForced = refl

notAcaciaReplacement :
  Q.chickpeaFertilizerEquivalentTransfersToAcaciaAvoidedMineralN
    Q.canonicalChickpeaEquivalentBoundary ≡ false
notAcaciaReplacement = refl
