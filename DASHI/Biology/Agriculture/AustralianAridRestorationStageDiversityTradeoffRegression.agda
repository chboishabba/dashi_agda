module DASHI.Biology.Agriculture.AustralianAridRestorationStageDiversityTradeoffRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AustralianAridRestorationStageDiversityTradeoffExact as T

bateman2019Pinned : T.batemanEtAl2019DOI ≡ "10.1016/j.jenvman.2019.04.022"
bateman2019Pinned = refl

bateman2019PMIDPinned : T.batemanEtAl2019PMID ≡ "30999267"
bateman2019PMIDPinned = refl

bateman2021Pinned : T.batemanEtAl2021DOI ≡ "10.1016/j.geoderma.2021.115001"
bateman2021Pinned = refl

earlyGrowthNotRecruitment :
  T.improvedLaterGrowthImpliesImprovedInitialRecruitment T.canonicalStageDiversityBoundary ≡ false
improvedLaterGrowthNotRecruitment = refl

initialSoilNNotPersistent :
  T.initialAmendmentSoilNIncreaseImpliesPersistentSoilNIncrease T.canonicalStageDiversityBoundary ≡ false
initialSoilNNotPersistent = refl

amendmentNotDominantDriver :
  T.inorganicAmendmentAloneDeterminesLongerTermSoilFunction T.canonicalStageDiversityBoundary ≡ false
amendmentNotDominantDriver = refl

stageTimeDiversityRetained :
  T.lifeStageTimePlantDiversityAndSubstrateMustRemainIndexed T.canonicalStageDiversityBoundary ≡ true
stageTimeDiversityRetained = refl

communityDiversityNotAuthority :
  T.diversePlantCommunityBenefitCreatesUniversalMixturePrescription T.canonicalStageDiversityBoundary ≡ false
communityDiversityNotAuthority = refl
