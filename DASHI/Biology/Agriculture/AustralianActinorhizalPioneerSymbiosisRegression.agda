module DASHI.Biology.Agriculture.AustralianActinorhizalPioneerSymbiosisRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AustralianActinorhizalPioneerSymbiosisExact as A

flemingEtAl1988DOIPinned :
  A.flemingEtAl1988DOI ≡ "10.1071/BT9880171"
flemingEtAl1988DOIPinned = refl

reddellBowen1985DOIPinned :
  A.reddellBowen1985DOI ≡ "10.1111/j.1469-8137.1985.tb02763.x"
reddellBowen1985DOIPinned = refl

reddellBowenRobson1985DOIPinned :
  A.reddellBowenRobson1985DOI ≡ "10.1111/j.1469-8137.1985.tb02850.x"
reddellBowenRobson1985DOIPinned = refl

reddellBowenRobson1985PMIDPinned :
  A.reddellBowenRobson1985PMID ≡ "33874228"
reddellBowenRobson1985PMIDPinned = refl

rosbrook1990DOIPinned :
  A.rosbrook1990DOI ≡ "10.1016/0378-1127(90)90021-3"
rosbrook1990DOIPinned = refl

nFixingRoleDoesNotIdentifyMechanism :
  A.sameNFixingPioneerRoleImpliesSameSymbioticMechanism A.canonicalActinorhizalBoundary ≡ false
nFixingRoleDoesNotIdentifyMechanism = refl

nodulePresenceDoesNotIdentifyFixation :
  A.nodulePresenceImpliesRealisedNitrogenFixation A.canonicalActinorhizalBoundary ≡ false
nodulePresenceDoesNotIdentifyFixation = refl

hostProvenanceRemainsIndexed :
  A.hostProvenanceMayBeDroppedFromFrankiaPerformance A.canonicalActinorhizalBoundary ≡ false
hostProvenanceRemainsIndexed = refl

temperatureRemainsIndexed :
  A.soilTemperatureMayBeDroppedFromSymbioticEnablement A.canonicalActinorhizalBoundary ≡ false
temperatureRemainsIndexed = refl

fieldAuthorityNotCreated :
  A.crossInoculationSuccessCreatesFieldDeploymentAuthority A.canonicalActinorhizalBoundary ≡ false
fieldAuthorityNotCreated = refl

acaciaLadderNotClosed :
  A.actinorhizalEvidenceClosesAcaciaReactionEnablement A.canonicalActinorhizalBoundary ≡ false
acaciaLadderNotClosed = refl
