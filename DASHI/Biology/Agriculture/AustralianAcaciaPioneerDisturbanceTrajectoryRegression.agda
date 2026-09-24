module DASHI.Biology.Agriculture.AustralianAcaciaPioneerDisturbanceTrajectoryRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AustralianAcaciaPioneerDisturbanceTrajectoryExact as P

andersen1993DOIPinned : P.andersen1993DOI ≡ "10.1111/j.1526-100X.1993.tb00022.x"
andersen1993DOIPinned = refl

bradyNoske2010DOIPinned : P.bradyNoske2010DOI ≡ "10.1111/j.1526-100X.2008.00511.x"
bradyNoske2010DOIPinned = refl

pioneerSuccessDoesNotGuaranteeRelease :
  P.pioneerEstablishmentImpliesSuccessfulSuccessionalRelease P.canonicalPioneerTrajectoryBoundary ≡ false
pioneerSuccessDoesNotGuaranteeRelease = refl

richnessDoesNotIdentifyReferenceComposition :
  P.referenceLikeRichnessImpliesReferenceLikeComposition P.canonicalPioneerTrajectoryBoundary ≡ false
richnessDoesNotIdentifyReferenceComposition = refl

fireRegimeRetained :
  P.disturbanceFireRegimeMustRemainIndexed P.canonicalPioneerTrajectoryBoundary ≡ true
fireRegimeRetained = refl

acaciaDominanceNotUniversalBenefit :
  P.acaciaDominanceImpliesLaterCommunityRecovery P.canonicalPioneerTrajectoryBoundary ≡ false
acaciaDominanceNotUniversalBenefit = refl
