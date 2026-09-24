module DASHI.Education.DigitalESDStudyEvidencePNFExtensionRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Education.DigitalESDStudyEvidencePNFExtensionExact as Ext
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF

studyEvidencePNFCountRegression : Ext.studyEvidencePNFCount ≡ 8
studyEvidencePNFCountRegression = refl

ardilaForceRegression :
  PNF.PredicateNormalAssertion.inferentialForce Ext.ardilaImplementationAssertion
  ≡ PNF.descriptiveF
ardilaForceRegression = refl

gousetiForceRegression :
  PNF.PredicateNormalAssertion.inferentialForce Ext.gousetiExperienceAssertion
  ≡ PNF.descriptiveF
gousetiForceRegression = refl

martinezForceRegression :
  PNF.PredicateNormalAssertion.inferentialForce Ext.martinezReviewAssertion
  ≡ PNF.descriptiveF
martinezForceRegression = refl

boehmeForceRegression :
  PNF.PredicateNormalAssertion.inferentialForce Ext.boehmeFrameworkAssertion
  ≡ PNF.descriptiveF
boehmeForceRegression = refl

pinzoneForceRegression :
  PNF.PredicateNormalAssertion.inferentialForce Ext.pinzoneScenarioAssertion
  ≡ PNF.comparativeF
pinzoneForceRegression = refl

holstForceRegression :
  PNF.PredicateNormalAssertion.inferentialForce Ext.holstMonitoringAssertion
  ≡ PNF.descriptiveF
holstForceRegression = refl

fishlockForceRegression :
  PNF.PredicateNormalAssertion.inferentialForce Ext.fishlockImplementationAssertion
  ≡ PNF.descriptiveF
fishlockForceRegression = refl

uneceForceRegression :
  PNF.PredicateNormalAssertion.inferentialForce Ext.uneceImplementationAssertion
  ≡ PNF.descriptiveF
uneceForceRegression = refl
