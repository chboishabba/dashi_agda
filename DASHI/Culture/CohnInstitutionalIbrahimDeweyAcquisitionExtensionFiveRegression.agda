module DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionFiveRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionFiveExact as Ext

indigenousRelationalResearchBurdenAdded :
  Ext.indigenousRelationalResearchBurdenAdded Ext.canonicalAcquisitionFiveBoundary ≡ true
indigenousRelationalResearchBurdenAdded = refl

knowledgeInclusionDoesNotPayRelation :
  Ext.knowledgeIncludedImpliesEthicalEquitableRelation Ext.canonicalAcquisitionFiveBoundary ≡ false
knowledgeInclusionDoesNotPayRelation = refl

engagementDoesNotEqualConsent :
  Ext.engagementImpliesConsentOrPermission Ext.canonicalAcquisitionFiveBoundary ≡ false
engagementDoesNotEqualConsent = refl

partnerDoesNotFlattenRightsHolder :
  Ext.indigenousRightsHolderMayBeFlattenedToGenericStakeholder Ext.canonicalAcquisitionFiveBoundary ≡ false
partnerDoesNotFlattenRightsHolder = refl

labourBurdenDoesNotBecomeSameConcept :
  Ext.reidRelationalLabourDefinitionallyEqualsBerenstainEpistemicLabour Ext.canonicalAcquisitionFiveBoundary ≡ false
labourBurdenDoesNotBecomeSameConcept = refl

careOcapAreReusedNotReacquired :
  Ext.careOcapGovernanceReused Ext.canonicalAcquisitionFiveBoundary ≡ true
careOcapAreReusedNotReacquired = refl

provenanceStillDoesNotDeterminePermission :
  Ext.provenanceAloneDeterminesPermission Ext.canonicalAcquisitionFiveBoundary ≡ false
provenanceStillDoesNotDeterminePermission = refl

ocapNotUniversalized :
  Ext.ocapMayBeUniversalizedAcrossAllIndigenousPeoples Ext.canonicalAcquisitionFiveBoundary ≡ false
ocapNotUniversalized = refl

sourceStillDoesNotSelectRepair :
  Ext.sourceAdjacencyAutomaticallySelectsResidual Ext.canonicalAcquisitionFiveBoundary ≡ false
sourceStillDoesNotSelectRepair = refl

qidFailClosed :
  Ext.unverifiedPublicationQidMayBeInvented Ext.canonicalAcquisitionFiveBoundary ≡ false
qidFailClosed = refl
