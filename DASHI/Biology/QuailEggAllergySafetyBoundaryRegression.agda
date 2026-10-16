module DASHI.Biology.QuailEggAllergySafetyBoundaryRegression where

open import DASHI.Core.Prelude using (⊥)
import DASHI.Biology.QuailEggAllergySafetyBoundaryExact as Q

caseReportRegression : Q.QuailEggAllergyEvidenceReceipt
caseReportRegression = Q.delgadoPrada2025Receipt

oralChallengeRegression : Q.QuailEggAllergyEvidenceReceipt
oralChallengeRegression = Q.yamashita2024Receipt

henToleranceNotQuailToleranceRegression :
  Q.HenEggToleranceImpliesQuailEggTolerancePermission → ⊥
henToleranceNotQuailToleranceRegression = Q.henToleranceDoesNotGuaranteeQuailTolerance

screeningRegression : Q.QuailEggInterventionSafetyRequirement
screeningRegression = Q.canonicalQuailEggInterventionSafetyRequirement

boundaryRegression : Q.QuailEggAllergySafetyBoundary
boundaryRegression = Q.canonicalQuailEggAllergySafetyBoundary
