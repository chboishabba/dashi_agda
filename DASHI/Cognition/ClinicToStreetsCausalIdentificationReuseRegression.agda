module DASHI.Cognition.ClinicToStreetsCausalIdentificationReuseRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)

import DASHI.Biology.CausalEffectEstimandExact as Estimand
import DASHI.Biology.CausalIdentificationFamiliesExact as Identification
import DASHI.Cognition.ClinicToStreetsEvidenceAcquisitionMaxCutExact as X

estimandOwnerReused : X.reusesCausalEffectEstimand ≡ true
estimandOwnerReused = refl

identificationOwnerReused : X.reusesCausalIdentificationFamilies ≡ true
identificationOwnerReused = refl

customEdgeChecklistRetired : X.reimplementsCausalIdentificationChecklist ≡ false
customEdgeChecklistRetired = refl

structuralFamilyTargetKind :
  X.CausalEdgeDemand.kind X.structuralToFamilyDemand ≡ Estimand.mediatedIndirectEffect
structuralFamilyTargetKind = refl

familyPsychicTargetKind :
  X.CausalEdgeDemand.kind X.familyToPsychicDemand ≡ Estimand.mediatedIndirectEffect
familyPsychicTargetKind = refl

structuralPsychicTargetKind :
  X.CausalEdgeDemand.kind X.structuralToPsychicDemand ≡ Estimand.controlledDirectEffect
structuralPsychicTargetKind = refl

preferredMediationFamily :
  X.CausalEdgeDemand.preferredIdentificationFamily X.structuralToFamilyDemand
  ≡ Identification.mechanisticMediation
preferredMediationFamily = refl

noCurrentIdentificationPayment : X.anyCurrentIdentificationReceiptPaid ≡ false
noCurrentIdentificationPayment = refl

attributedSourceNotCausalProof : X.attributedClaimsAreEmpiricalCausalProof ≡ false
attributedSourceNotCausalProof = refl
