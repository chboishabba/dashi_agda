module DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionThreeRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionThreeExact as Acquisition

structuralEpistemicExclusionAdded :
  Acquisition.structuralEpistemicExclusionAdded
    Acquisition.canonicalAcquisitionThreeBoundary ≡ true
structuralEpistemicExclusionAdded = refl

epistemicLabourBurdenAdded :
  Acquisition.epistemicLabourBurdenAdded
    Acquisition.canonicalAcquisitionThreeBoundary ≡ true
epistemicLabourBurdenAdded = refl

outsiderWithinStandpointAdded :
  Acquisition.outsiderWithinStandpointAdded
    Acquisition.canonicalAcquisitionThreeBoundary ≡ true
outsiderWithinStandpointAdded = refl

participationPowerAdded :
  Acquisition.participationPowerAdded
    Acquisition.canonicalAcquisitionThreeBoundary ≡ true
participationPowerAdded = refl

twoEyedCoexistenceActionAdded :
  Acquisition.twoEyedCoexistenceActionAdded
    Acquisition.canonicalAcquisitionThreeBoundary ≡ true
twoEyedCoexistenceActionAdded = refl

presenceDoesNotEqualDecisionPower :
  Acquisition.presenceEqualsDecisionPower
    Acquisition.canonicalAcquisitionThreeBoundary ≡ false
presenceDoesNotEqualDecisionPower = refl

coexistenceDoesNotEqualFusion :
  Acquisition.twoEyedCoexistenceEqualsEpistemicFusion
    Acquisition.canonicalAcquisitionThreeBoundary ≡ false
coexistenceDoesNotEqualFusion = refl

sourceDoesNotSelectRepair :
  Acquisition.sourceIdentityAutomaticallySelectsResidual
    Acquisition.canonicalAcquisitionThreeBoundary ≡ false
sourceDoesNotSelectRepair = refl

newFamiliesRemainCandidateOnly :
  Acquisition.acquisitionCreatesInstitutionalFact
    Acquisition.canonicalAcquisitionThreeBoundary ≡ false
newFamiliesRemainCandidateOnly = refl
