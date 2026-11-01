module DASHI.Education.DigitalESDOpenCommonsSituatedMaterialRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Education.DigitalESDOpenCommonsSituatedMaterialExact as Bridge
import DASHI.Education.DigitalESDStudyIntersectionalAbsenceAuditExact as Absence
import DASHI.Education.DigitalESDMaterialEnvironmentalSubstrateExact as Material
import DASHI.Ontology.DeweyQidCoverageQualityExact as Identity

absenceQuestionCountRegression : Bridge.absenceQuestionCount ≡ Absence.absenceAuditQuestionCount
absenceQuestionCountRegression = refl

materialStageCountRegression : Bridge.materialStageCount ≡ Material.digitalMaterialStageCount
materialStageCountRegression = refl

qidBoundaryRegression : Bridge.qidCoverageBoundary ≡ Identity.canonicalCoverageQualityBoundary
qidBoundaryRegression = refl

openCommonsDoesNotCloseAbsenceRegression :
  Bridge.OpenCommonsBoundary.openCommonsClosesWhoMissingAudit Bridge.canonicalOpenCommonsBoundary ≡ false
openCommonsDoesNotCloseAbsenceRegression = refl

openCommonsDoesNotCloseMaterialRegression :
  Bridge.OpenCommonsBoundary.openCommonsClosesMaterialAudit Bridge.canonicalOpenCommonsBoundary ≡ false
openCommonsDoesNotCloseMaterialRegression = refl
