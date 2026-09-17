module DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionFourRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionFourExact as Ext

medinaEpistemicActivismAdded :
  Ext.medinaEpistemicActivismAdded Ext.canonicalAcquisitionFourBoundary ≡ true
medinaEpistemicActivismAdded = refl

youngInternalExclusionAdded :
  Ext.youngInternalExclusionAdded Ext.canonicalAcquisitionFourBoundary ≡ true
youngInternalExclusionAdded = refl

bartlettTwoEyedSourceReused :
  Ext.bartlettTwoEyedSourceReused Ext.canonicalAcquisitionFourBoundary ≡ true
bartlettTwoEyedSourceReused = refl

formalPresenceDoesNotDetermineInfluence :
  Ext.formalPresenceDeterminesEffectiveCommunicativeInfluence Ext.canonicalAcquisitionFourBoundary ≡ false
formalPresenceDoesNotDetermineInfluence = refl

protestDoesNotBecomeProof :
  Ext.protestCreatesProofAuthority Ext.canonicalAcquisitionFourBoundary ≡ false
protestDoesNotBecomeProof = refl

coLearningDoesNotFuseEpistemologies :
  Ext.twoEyedCoLearningImpliesEpistemicFusion Ext.canonicalAcquisitionFourBoundary ≡ false
coLearningDoesNotFuseEpistemologies = refl

publicationQidsRemainFailClosed :
  Ext.unverifiedPublicationQidMayBeInvented Ext.canonicalAcquisitionFourBoundary ≡ false
publicationQidsRemainFailClosed = refl

newSourcesStillRequireFibreTest :
  Ext.sourceAdjacencyAutomaticallySelectsResidual Ext.canonicalAcquisitionFourBoundary ≡ false
newSourcesStillRequireFibreTest = refl
