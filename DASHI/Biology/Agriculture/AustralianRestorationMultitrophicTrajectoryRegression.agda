module DASHI.Biology.Agriculture.AustralianRestorationMultitrophicTrajectoryRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AustralianRestorationMultitrophicTrajectoryExact as T

majerNichols1998DOIPinned :
  T.majerNichols1998DOI ≡ "10.1046/j.1365-2664.1998.00286.x"
majerNichols1998DOIPinned = refl

majerEtAl2013DOIPinned :
  T.majerEtAl2013DOI ≡ "10.1186/2192-1709-2-19"
majerEtAl2013DOIPinned = refl

vanDerHeyde2022DOIPinned :
  T.vanDerHeydeEtAl2022DOI ≡ "10.1111/mec.16375"
vanDerHeyde2022DOIPinned = refl

vanDerHeyde2022PMIDPinned : T.vanDerHeydeEtAl2022PMID ≡ "35092102"
vanDerHeyde2022PMIDPinned = refl

earlyRankingDoesNotDetermineLongTermRanking :
  T.earlyTreatmentRankingImpliesThirtySevenYearRanking T.canonicalMultitrophicBoundary ≡ false
earlyRankingDoesNotDetermineLongTermRanking = refl

richnessDoesNotDetermineComposition :
  T.richnessRecoveryImpliesCompositionRecovery T.canonicalMultitrophicBoundary ≡ false
richnessDoesNotDetermineComposition = refl

referenceStateIsTimeIndexed :
  T.referenceCommunityMayBeTreatedAsTimeInvariant T.canonicalMultitrophicBoundary ≡ false
referenceStateIsTimeIndexed = refl

plantCoverDoesNotDetermineFaunalRecovery :
  T.plantCoverSimilarityImpliesFaunalReferenceConvergence T.canonicalMultitrophicBoundary ≡ false
plantCoverDoesNotDetermineFaunalRecovery = refl

guildMobilityRemainsIndexed :
  T.indicatorGuildMobilityMustRemainIndexed T.canonicalMultitrophicBoundary ≡ true
guildMobilityRemainsIndexed = refl

chronosequenceDoesNotReplaceLongitudinalObservation :
  T.chronosequenceCanReplaceLongitudinalObservation T.canonicalMultitrophicBoundary ≡ false
chronosequenceDoesNotReplaceLongitudinalObservation = refl
