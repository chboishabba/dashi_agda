module DASHI.Education.DigitalESDDBNativeAcademicWorldExecutionRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDDBNativeAcademicWorldExecutionExact as DB
import DASHI.Education.DigitalESDCandidateWorldExecutionExact as World
import DASHI.Education.DigitalESDManuscriptMethodologyExact as Methodology

worldBoundaryRegression :
  DB.candidateWorldBoundary
  ≡ World.canonicalDigitalESDCandidateWorldExecutionBoundary
worldBoundaryRegression = refl

nineteenCoordinateRegression :
  DB.extractionCoordinateCount ≡ Methodology.extractionCoordinateCount
nineteenCoordinateRegression = refl

parserNominationPaymentRegression :
  DB.ParserNominationPaysExtractionCoordinate → ⊥
parserNominationPaymentRegression =
  DB.parserNominationDoesNotPayExtractionCoordinate

missingNominationAbsenceRegression :
  DB.MissingNominationCreatesAbsenceFact → ⊥
missingNominationAbsenceRegression =
  DB.missingNominationDoesNotCreateAbsenceFact

sameStudyPromotionRegression :
  DB.GenealogyHypothesisCreatesSameEmpiricalStudy → ⊥
sameStudyPromotionRegression =
  DB.genealogyHypothesisDoesNotCreateSameEmpiricalStudy

independencePromotionRegression :
  DB.GenealogyHypothesisCreatesEvidenceIndependence → ⊥
independencePromotionRegression =
  DB.genealogyHypothesisDoesNotCreateEvidenceIndependence


nominationClaimTruthRegression :
  DB.DBNativeCoordinateNominationBoundary.nominationCreatesClaimTruth
    DB.canonicalDBNativeCoordinateNominationBoundary ≡ false
nominationClaimTruthRegression = refl

workflowOrderRankRegression :
  DB.WorkflowOrderCreatesEvidenceQualityRank → ⊥
workflowOrderRankRegression =
  DB.workflowOrderDoesNotCreateEvidenceQualityRank
