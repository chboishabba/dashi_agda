module DASHI.Education.DigitalESDStudyClaimMethodBridgeRegression where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Education.DigitalESDStudyClaimMethodBridgeExact as Method

intersectionalAbsenceRequiredRegression :
  Method.StudyClaimMethodBoundary.intersectionalAbsenceAuditRequired
    Method.canonicalStudyClaimMethodBoundary ≡ true
intersectionalAbsenceRequiredRegression = refl

materialSubstrateRequiredRegression :
  Method.StudyClaimMethodBoundary.materialEnvironmentalAuditRequired
    Method.canonicalStudyClaimMethodBoundary ≡ true
materialSubstrateRequiredRegression = refl

paidPNFRequiredRegression :
  Method.StudyClaimMethodBoundary.predicateLevelResultAuditRequired
    Method.canonicalStudyClaimMethodBoundary ≡ true
paidPNFRequiredRegression = refl
