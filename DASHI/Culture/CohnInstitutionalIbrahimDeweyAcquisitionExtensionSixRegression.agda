module DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionSixRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionSixExact as Ext

eligibleButMissingFamilyAdded :
  Ext.eligibleButMissingFamilyAdded Ext.canonicalAcquisitionSixBoundary ≡ true
eligibleButMissingFamilyAdded = refl

nonDisclosureGateAdded :
  Ext.nonDisclosureGateAdded Ext.canonicalAcquisitionSixBoundary ≡ true
nonDisclosureGateAdded = refl

surveyNonresponseGateAdded :
  Ext.surveyNonresponseGateAdded Ext.canonicalAcquisitionSixBoundary ≡ true
surveyNonresponseGateAdded = refl

differentialConsentGateAdded :
  Ext.differentialConsentGateAdded Ext.canonicalAcquisitionSixBoundary ≡ true
differentialConsentGateAdded = refl

realisedCarrierNotEligiblePopulation :
  Ext.realisedCarrierEqualsEligiblePopulation Ext.canonicalAcquisitionSixBoundary ≡ false
realisedCarrierNotEligiblePopulation = refl

nonDisclosureDoesNotMeanAbsence :
  Ext.nonDisclosureMeansNoDisability Ext.canonicalAcquisitionSixBoundary ≡ false
nonDisclosureDoesNotMeanAbsence = refl

nonresponseNotAssumedIgnorable :
  Ext.nonresponseMayBeIgnoredWithoutEvidence Ext.canonicalAcquisitionSixBoundary ≡ false
nonresponseNotAssumedIgnorable = refl

consentMissingnessNotAssumedRandom :
  Ext.differentialConsentMayBeTreatedAsRandomMissingness Ext.canonicalAcquisitionSixBoundary ≡ false
consentMissingnessNotAssumedRandom = refl

sourceStillDoesNotCreateWorldFact :
  Ext.sourceCreatesInstitutionalFact Ext.canonicalAcquisitionSixBoundary ≡ false
sourceStillDoesNotCreateWorldFact = refl

qidStillFailClosed :
  Ext.unverifiedPublicationQidMayBeInvented Ext.canonicalAcquisitionSixBoundary ≡ false
qidStillFailClosed = refl
