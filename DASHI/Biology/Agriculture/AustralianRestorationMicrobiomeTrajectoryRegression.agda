module DASHI.Biology.Agriculture.AustralianRestorationMicrobiomeTrajectoryRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AustralianRestorationMicrobiomeTrajectoryExact as M

gellie2017Pinned : M.gellieEtAl2017DOI ≡ "10.1111/mec.14081"
gellie2017Pinned = refl

ngugi2018Pinned : M.ngugiEtAl2018DOI ≡ "10.1111/rec.12631"
ngugi2018Pinned = refl

lem2022Pinned : M.lemEtAl2022DOI ≡ "10.1111/rec.13635"
lem2022Pinned = refl

peddle2023Pinned : M.peddleEtAl2023DOI ≡ "10.1111/rec.13706"
peddle2023Pinned = refl

chronosequenceNotLongitudinalCausality :
  M.chronosequenceSimilarityImpliesLongitudinalCausalRecovery M.canonicalMicrobiomeTrajectoryBoundary ≡ false
chronosequenceNotLongitudinalCausality = refl

alphaDiversityNotComposition :
  M.alphaDiversityRecoveryImpliesCommunityCompositionRecovery M.canonicalMicrobiomeTrajectoryBoundary ≡ false
alphaDiversityNotComposition = refl

samplingContextRetained :
  M.samplingSeasonSoilChemistryAndReferenceChoiceMustRemainIndexed M.canonicalMicrobiomeTrajectoryBoundary ≡ true
samplingContextRetained = refl

microbiomeNotWholeEcosystem :
  M.microbiomeReferenceSimilarityImpliesWholeEcosystemRecovery M.canonicalMicrobiomeTrajectoryBoundary ≡ false
microbiomeNotWholeEcosystem = refl
