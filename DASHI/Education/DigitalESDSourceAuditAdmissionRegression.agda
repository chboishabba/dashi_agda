module DASHI.Education.DigitalESDSourceAuditAdmissionRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDSourceAuditAdmissionExact as Admission

noGrandTotalPinned : Admission.AuthoritativeGrandTotalExists → ⊥
noGrandTotalPinned = Admission.authoritativeGrandTotalDoesNotExist

unscoredSourceNoSynthesis : Admission.UnscoredSourceEntersSynthesis → ⊥
unscoredSourceNoSynthesis = Admission.unscoredSourceDoesNotEnterSynthesis

admissionNoAuthority : Admission.AuditAdmissionCreatesClaimAuthority → ⊥
admissionNoAuthority = Admission.auditAdmissionDoesNotCreateClaimAuthority
