module DASHI.Wikimedia.IbrahimCannabisThermalTransferEvidenceGradeRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

------------------------------------------------------------------------
-- RED regression surface for route-specific cannabis contaminant transfer.
--
-- Required behaviour:
--   * distinguish direct cannabis smoke-transfer evidence from
--     non-cannabis thermal-degradation evidence and mere prediction;
--   * retain smoking-device dependence;
--   * do not promote vape-fluid occurrence into aerosol-transfer evidence;
--   * do not promote possible thermal products into measured inhaled dose;
--   * retain the low-risk Health Canada interpretation for recalled
--     myclobutanil concentrations separately from generic decomposition claims.
------------------------------------------------------------------------

data EvidenceGrade : Set where
  directCannabisSmokeTransfer : EvidenceGrade
  directCannabisVapeAerosolTransfer : EvidenceGrade
  cannabisProductOccurrenceOnly : EvidenceGrade
  nonCannabisThermalTransformation : EvidenceGrade
  mechanisticPredictionOnly : EvidenceGrade
  unresolved : EvidenceGrade

record RegressionRequirement : Set where
  constructor regression-requirement
  field
    gradesSeparated : Bool
    gradesSeparatedIsTrue : gradesSeparated ≡ true
    deviceDependenceRetained : Bool
    deviceDependenceRetainedIsTrue : deviceDependenceRetained ≡ true
    occurrenceIsNotTransfer : Bool
    occurrenceIsNotTransferIsTrue : occurrenceIsNotTransfer ≡ true
    transformationIsNotDose : Bool
    transformationIsNotDoseIsTrue : transformationIsNotDose ≡ true
    recalledMyclobutanilRiskInterpretationRetained : Bool
    recalledMyclobutanilRiskInterpretationRetainedIsTrue : recalledMyclobutanilRiskInterpretationRetained ≡ true

canonicalRegressionRequirement : RegressionRequirement
canonicalRegressionRequirement = regression-requirement
  true refl true refl true refl true refl true refl
