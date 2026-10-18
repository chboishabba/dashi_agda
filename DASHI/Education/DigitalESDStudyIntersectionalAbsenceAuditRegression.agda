module DASHI.Education.DigitalESDStudyIntersectionalAbsenceAuditRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDStudyIntersectionalAbsenceAuditExact as Audit
import DASHI.Core.IntersectionalNonFactorability as Intersection

questionCountRegression : Audit.absenceAuditQuestionCount ≡ 11
questionCountRegression = refl

disabilitySourceCountRegression : Audit.disabilitySourceCount ≡ 4
disabilitySourceCountRegression = refl

sampleSizeCannotDetermineRepresentationRegression :
  Intersection.FactorsThrough Audit.sampleSizeProjection Audit.representationAdequacy → ⊥
sampleSizeCannotDetermineRepresentationRegression =
  Audit.sampleSizeCannotDetermineRepresentationAdequacy

noDiagnosisFromEngagementRegression : Audit.EngagementSurfaceCreatesDisabilityOrTraumaDiagnosis → ⊥
noDiagnosisFromEngagementRegression = Audit.engagementDoesNotCreateDisabilityOrTraumaDiagnosis
