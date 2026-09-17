module DASHI.Biology.Agriculture.AustralianGrasslandSuccessionRegenerationRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AustralianGrasslandSuccessionRegenerationExact as G

scottMorgan2012Pinned : G.scottMorgan2012DOI ≡ "10.1016/j.jaridenv.2011.08.014"
scottMorgan2012Pinned = refl

standish2007Pinned : G.standish2007DOI ≡ "10.1111/j.1365-2664.2006.01262.x"
standish2007Pinned = refl

fensham2016Pinned : G.fensham2016DOI ≡ "10.1111/1365-2664.12551"
fensham2016Pinned = refl

parkhurst2022Pinned : G.parkhurst2022DOI ≡ "10.1002/eap.2547"
parkhurst2022Pinned = refl

parkhurstPMIDPinned : G.parkhurst2022PMID ≡ "35080806"
parkhurstPMIDPinned = refl

johnson2025Pinned : G.johnsonEtAl2025DOI ≡ "10.1016/j.ecoleng.2025.107724"
johnson2025Pinned = refl

soilNotFlora : G.soilRecoveryImpliesFloristicRecovery G.canonicalGrasslandBoundary ≡ false
soilNotFlora = refl

passiveNotGuaranteed : G.abandonmentImpliesReferenceCommunityRecovery G.canonicalGrasslandBoundary ≡ false
passiveNotGuaranteed = refl

seedContextRetained : G.seedSourceDispersalAndRecruitmentMustRemainIndexed G.canonicalGrasslandBoundary ≡ true
seedContextRetained = refl

presentVegetationNotEraseP : G.presentVegetationErasesAgriculturalPLegacy G.canonicalGrasslandBoundary ≡ false
presentVegetationNotEraseP = refl

regulatoryTargetNotReferenceTrajectory :
  G.regulatoryTargetAttainmentImpliesSelfSustainingReferenceTrajectory G.canonicalGrasslandBoundary ≡ false
regulatoryTargetNotReferenceTrajectory = refl

canopyTargetNotNativeGrassRecovery :
  G.woodyCanopyTargetAttainmentImpliesNativeGrassRecovery G.canonicalGrasslandBoundary ≡ false
canopyTargetNotNativeGrassRecovery = refl

exoticCompetitionRetained :
  G.exoticPastureCompetitionMayBeDropped G.canonicalGrasslandBoundary ≡ false
exoticCompetitionRetained = refl

threeYearsNotLongTerm :
  G.thirtySixMonthSuccessImpliesLongTermTrajectorySuccess G.canonicalGrasslandBoundary ≡ false
threeYearsNotLongTerm = refl
