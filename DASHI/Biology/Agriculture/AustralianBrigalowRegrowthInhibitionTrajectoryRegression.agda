module DASHI.Biology.Agriculture.AustralianBrigalowRegrowthInhibitionTrajectoryRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AustralianBrigalowRegrowthInhibitionTrajectoryExact as B

johnsonEtAl2016DOIPinned :
  B.johnsonEtAl2016DOI ≡ "10.1111/aec.12354"
johnsonEtAl2016DOIPinned = refl

dwyerMason2018DOIPinned :
  B.dwyerMason2018DOI ≡ "10.1111/rec.12536"
dwyerMason2018DOIPinned = refl

leBrocqueWagner2018DOIPinned :
  B.leBrocqueWagner2018DOI ≡ "10.1111/aec.12578"
leBrocqueWagner2018DOIPinned = refl

regrowthDominanceDoesNotEqualRelease :
  B.brigalowRegrowthAbundanceImpliesReleasedSuccession B.canonicalBrigalowBoundary ≡ false
regrowthDominanceDoesNotEqualRelease = refl

structureDoesNotEqualComposition :
  B.standStructureRecoveryImpliesFloristicCompositionRecovery B.canonicalBrigalowBoundary ≡ false
structureDoesNotEqualComposition = refl

thinningDoesNotGuaranteeComposition :
  B.thinningIncreasesRecruitmentImpliesReferenceComposition B.canonicalBrigalowBoundary ≡ false
thinningDoesNotGuaranteeComposition = refl

herbaceousAndWoodyTrajectoriesStaySeparate :
  B.herbaceousAndWoodyDiversityMayBeCollapsed B.canonicalBrigalowBoundary ≡ false
herbaceousAndWoodyTrajectoriesStaySeparate = refl

landscapeContextRemainsIndexed :
  B.dispersalLandscapeGrazingAndSoilContextMustRemainIndexed B.canonicalBrigalowBoundary ≡ true
landscapeContextRemainsIndexed = refl
