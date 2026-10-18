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

medinaAuthorQidResolved :
  Ext.medinaAuthorQidResolved Ext.canonicalAcquisitionFourBoundary ≡ true
medinaAuthorQidResolved = refl

youngAuthorQidResolved :
  Ext.youngAuthorQidResolved Ext.canonicalAcquisitionFourBoundary ≡ true
youngAuthorQidResolved = refl

medinaPublicationQidStillUnresolved :
  Ext.medinaPublicationQidResolved Ext.canonicalAcquisitionFourBoundary ≡ false
medinaPublicationQidStillUnresolved = refl

youngPublicationQidStillUnresolved :
  Ext.youngPublicationQidResolved Ext.canonicalAcquisitionFourBoundary ≡ false
youngPublicationQidStillUnresolved = refl

publicationSpecificDeweyStillUnresolved :
  Ext.publicationSpecificDeweyVerified Ext.canonicalAcquisitionFourBoundary ≡ false
publicationSpecificDeweyStillUnresolved = refl

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
