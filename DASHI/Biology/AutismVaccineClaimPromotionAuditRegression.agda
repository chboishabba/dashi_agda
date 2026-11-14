module DASHI.Biology.AutismVaccineClaimPromotionAuditRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.AutismVaccineClaimPromotionAuditExact as P

sourceVoicesRemainSeparated :
  P.sourceVoicesSeparated P.canonicalAuditBoundary ≡ true
sourceVoicesRemainSeparated = refl

sourceReportDoesNotCreateTruth :
  P.sourceReportCreatesTruth P.canonicalAuditBoundary ≡ false
sourceReportDoesNotCreateTruth = refl

associationDoesNotCreateCausation :
  P.associationCreatesCausation P.canonicalAuditBoundary ≡ false
associationDoesNotCreateCausation = refl

scaleCutoffDoesNotEraseDiagnosis :
  P.symptomCutoffEqualsDiagnosisRemoval P.canonicalAuditBoundary ≡ false
scaleCutoffDoesNotEraseDiagnosis = refl

synchronyDoesNotCreateFalseBelief :
  P.synchronyCreatesFalseBelief P.canonicalAuditBoundary ≡ false
synchronyDoesNotCreateFalseBelief = refl

pronounsDoNotDiagnoseIndividual :
  P.pronounCountDiagnosesIndividual P.canonicalAuditBoundary ≡ false
pronounsDoNotDiagnoseIndividual = refl

mediaPropagationIsSeparateFromBiomedicalTruth :
  P.mediaPropagationDeterminesBiomedicalTruth P.canonicalAuditBoundary ≡ false
mediaPropagationIsSeparateFromBiomedicalTruth = refl

vaccineAutismCausalPromotionBlocked :
  P.edgeStatus P.vaccineToAutismEdge ≡ P.blockedPromotion
vaccineAutismCausalPromotionBlocked = refl

fmtDiagnosisRemovalPromotionBlocked :
  P.edgeStatus P.fmtToDiagnosisRemovalEdge ≡ P.blockedPromotion
fmtDiagnosisRemovalPromotionBlocked = refl

synchronyFalseBeliefPromotionBlocked :
  P.edgeStatus P.synchronyToFalseBeliefEdge ≡ P.blockedPromotion
synchronyFalseBeliefPromotionBlocked = refl

hbombSourceClaimsRemainAttributed :
  P.claimSpeaker P.hbombAutismRepresentationClaim ≡ P.hbomberguy
hbombSourceClaimsRemainAttributed = refl

wakefieldMechanismRemainsWakefieldAttributed :
  P.claimSpeaker P.wakefieldGutOpioidMechanismClaim ≡ P.wakefield
wakefieldMechanismRemainsWakefieldAttributed = refl
