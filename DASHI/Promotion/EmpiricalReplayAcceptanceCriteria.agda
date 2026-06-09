module DASHI.Promotion.EmpiricalReplayAcceptanceCriteria where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Level; Setω)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Promotion.EmpiricalRuntimeReplayAdapter as Replay
import DASHI.Promotion.NumericAndAuthorityObligations as Authority

------------------------------------------------------------------------
-- Empirical replay acceptance criteria.
--
-- This module sits one layer above the deterministic replay adapter.  It
-- records which acceptance criteria are genuinely inhabited by the canonical
-- replay report and which are still blocked by absent authority/proof tokens.

listCount : ∀ {a : Level} {A : Set a} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

data AcceptanceCriterionName : Set where
  providerAuthorityTokenCriterion : AcceptanceCriterionName
  sourceChecksumMatchCriterion : AcceptanceCriterionName
  observableDefinitionAcceptanceCriterion : AcceptanceCriterionName
  projectionTransformLawCriterion : AcceptanceCriterionName
  comparisonLawAcceptanceCriterion : AcceptanceCriterionName
  covarianceUnitCalibrationCriterion : AcceptanceCriterionName
  holdoutProtocolPassCriterion : AcceptanceCriterionName
  runtimeCommandReproducibilityCriterion : AcceptanceCriterionName
  parserReducerVersionPinCriterion : AcceptanceCriterionName
  semanticReviewAcceptanceCriterion : AcceptanceCriterionName

data AcceptanceDisposition : Set where
  criterionPassesLocally : AcceptanceDisposition
  criterionFailsMissingAuthority : AcceptanceDisposition
  criterionFailsMissingReview : AcceptanceDisposition

record AcceptanceCriterionRow : Set₁ where
  field
    criterionName : AcceptanceCriterionName
    criterionLabel : String
    governingObligation : Authority.AuthorityObligationRow
    disposition : AcceptanceDisposition
    passes : Bool
    failsOrMissing : Bool
    externalAuthorityRequired : Bool
    evidenceNote : String
    missingEvidenceNote : String

open AcceptanceCriterionRow public

mkLocalPassCriterion :
  AcceptanceCriterionName →
  String →
  Authority.AuthorityObligationRow →
  String →
  AcceptanceCriterionRow
mkLocalPassCriterion name label obligation evidence =
  record
    { criterionName = name
    ; criterionLabel = label
    ; governingObligation = obligation
    ; disposition = criterionPassesLocally
    ; passes = true
    ; failsOrMissing = false
    ; externalAuthorityRequired = false
    ; evidenceNote = evidence
    ; missingEvidenceNote =
        "no missing authority for this local replay equality criterion"
    }

mkAuthorityFailCriterion :
  AcceptanceCriterionName →
  String →
  Authority.AuthorityObligationRow →
  String →
  AcceptanceCriterionRow
mkAuthorityFailCriterion name label obligation missing =
  record
    { criterionName = name
    ; criterionLabel = label
    ; governingObligation = obligation
    ; disposition = criterionFailsMissingAuthority
    ; passes = false
    ; failsOrMissing = true
    ; externalAuthorityRequired = true
    ; evidenceNote =
        "canonical validation report is fail-closed for this authority criterion"
    ; missingEvidenceNote = missing
    }

mkReviewFailCriterion :
  AcceptanceCriterionName →
  String →
  Authority.AuthorityObligationRow →
  String →
  AcceptanceCriterionRow
mkReviewFailCriterion name label obligation missing =
  record
    { criterionName = name
    ; criterionLabel = label
    ; governingObligation = obligation
    ; disposition = criterionFailsMissingReview
    ; passes = false
    ; failsOrMissing = true
    ; externalAuthorityRequired = true
    ; evidenceNote =
        "canonical validation report does not infer semantic adequacy from replay"
    ; missingEvidenceNote = missing
    }

------------------------------------------------------------------------
-- Canonical criteria rows.

providerAuthorityTokenRow : AcceptanceCriterionRow
providerAuthorityTokenRow =
  mkAuthorityFailCriterion
    providerAuthorityTokenCriterion
    "provider authority token accepted"
    Authority.providerAuthorityObligation
    "provider authority decision token is absent"

sourceChecksumMatchRow : AcceptanceCriterionRow
sourceChecksumMatchRow =
  mkLocalPassCriterion
    sourceChecksumMatchCriterion
    "source checksum matches runtime environment"
    Authority.providerAuthorityObligation
    "Replay.canonicalSourceChecksumMatchesEnvironment is inhabited"

observableDefinitionAcceptanceRow : AcceptanceCriterionRow
observableDefinitionAcceptanceRow =
  mkAuthorityFailCriterion
    observableDefinitionAcceptanceCriterion
    "observable definition accepted by provider authority"
    Authority.providerAuthorityObligation
    "observable-class authority receipt is absent"

projectionTransformLawRow : AcceptanceCriterionRow
projectionTransformLawRow =
  mkAuthorityFailCriterion
    projectionTransformLawCriterion
    "projection transform law accepted"
    Authority.comparisonLawObligation
    "projection transform law theorem/adapter receipt is absent"

comparisonLawAcceptanceRow : AcceptanceCriterionRow
comparisonLawAcceptanceRow =
  mkAuthorityFailCriterion
    comparisonLawAcceptanceCriterion
    "comparison law accepted"
    Authority.comparisonLawObligation
    "comparison law theorem/adapter receipt is absent"

covarianceUnitCalibrationRow : AcceptanceCriterionRow
covarianceUnitCalibrationRow =
  mkAuthorityFailCriterion
    covarianceUnitCalibrationCriterion
    "covariance and unit calibration accepted"
    Authority.covarianceCalibrationObligation
    "covariance matrix, unit, calibration, and uncertainty authority is absent"

holdoutProtocolPassRow : AcceptanceCriterionRow
holdoutProtocolPassRow =
  mkAuthorityFailCriterion
    holdoutProtocolPassCriterion
    "holdout protocol passes"
    Authority.holdoutValidationObligation
    "holdout dataset authority and frozen evaluation log receipts are absent"

runtimeCommandReproducibilityRow : AcceptanceCriterionRow
runtimeCommandReproducibilityRow =
  mkLocalPassCriterion
    runtimeCommandReproducibilityCriterion
    "runtime command is reproducible for identical replay log"
    Authority.runtimeReplayObligation
    "Replay.canonicalIdenticalReplayProjectionDigest and log digest equality are inhabited"

parserReducerVersionPinRow : AcceptanceCriterionRow
parserReducerVersionPinRow =
  mkAuthorityFailCriterion
    parserReducerVersionPinCriterion
    "parser and reducer version pin accepted"
    Authority.runtimeReplayObligation
    "environment lock, parser version, and reducer version authority receipt is absent"

semanticReviewAcceptanceRow : AcceptanceCriterionRow
semanticReviewAcceptanceRow =
  mkReviewFailCriterion
    semanticReviewAcceptanceCriterion
    "semantic adequacy review accepted"
    Authority.semanticAdequacyObligation
    "semantic review authority receipt is absent"

canonicalPassingAcceptanceCriteria : List AcceptanceCriterionRow
canonicalPassingAcceptanceCriteria =
  sourceChecksumMatchRow
  ∷ runtimeCommandReproducibilityRow
  ∷ []

canonicalFailingAcceptanceCriteria : List AcceptanceCriterionRow
canonicalFailingAcceptanceCriteria =
  providerAuthorityTokenRow
  ∷ observableDefinitionAcceptanceRow
  ∷ projectionTransformLawRow
  ∷ comparisonLawAcceptanceRow
  ∷ covarianceUnitCalibrationRow
  ∷ holdoutProtocolPassRow
  ∷ parserReducerVersionPinRow
  ∷ semanticReviewAcceptanceRow
  ∷ []

canonicalAcceptanceCriteriaRows : List AcceptanceCriterionRow
canonicalAcceptanceCriteriaRows =
  providerAuthorityTokenRow
  ∷ sourceChecksumMatchRow
  ∷ observableDefinitionAcceptanceRow
  ∷ projectionTransformLawRow
  ∷ comparisonLawAcceptanceRow
  ∷ covarianceUnitCalibrationRow
  ∷ holdoutProtocolPassRow
  ∷ runtimeCommandReproducibilityRow
  ∷ parserReducerVersionPinRow
  ∷ semanticReviewAcceptanceRow
  ∷ []

------------------------------------------------------------------------
-- Canonical evaluation.

record EmpiricalReplayAcceptanceEvaluation : Setω where
  field
    evaluationLabel : String
    authorityIndex : Authority.NumericAndAuthorityObligationIndex
    sourceValidationReport : Replay.EmpiricalRuntimeValidationReport
    criteriaRows : List AcceptanceCriterionRow
    passingCriteria : List AcceptanceCriterionRow
    failingCriteria : List AcceptanceCriterionRow
    criterionCount : Nat
    criterionCountMatches :
      criterionCount ≡ listCount criteriaRows
    passCount : Nat
    passCountMatches :
      passCount ≡ listCount passingCriteria
    failCount : Nat
    failCountMatches :
      failCount ≡ listCount failingCriteria
    deterministicReplayCriterionPasses : Bool
    deterministicReplayCriterionPassesIsTrue :
      deterministicReplayCriterionPasses ≡ true
    sourceChecksumCriterionPasses : Bool
    sourceChecksumCriterionPassesIsTrue :
      sourceChecksumCriterionPasses ≡ true
    allExternalAuthorityCriteriaFail : Bool
    allExternalAuthorityCriteriaFailIsTrue :
      allExternalAuthorityCriteriaFail ≡ true
    validationVerdictStillFails :
      Replay.EmpiricalRuntimeValidationReport.validationVerdict
        sourceValidationReport
      ≡
      Replay.validationFail Replay.canonicalValidationFailureReasons
    semanticAdequacyAccepted : Bool
    semanticAdequacyAcceptedIsFalse :
      semanticAdequacyAccepted ≡ false
    empiricalAdequacyAccepted : Bool
    empiricalAdequacyAcceptedIsFalse :
      empiricalAdequacyAccepted ≡ false

open EmpiricalReplayAcceptanceEvaluation public

canonicalEmpiricalReplayAcceptanceEvaluation :
  EmpiricalReplayAcceptanceEvaluation
canonicalEmpiricalReplayAcceptanceEvaluation = record
  { evaluationLabel =
      "empirical replay acceptance criteria over canonical fail-closed report"
  ; authorityIndex =
      Authority.canonicalNumericAndAuthorityObligationIndex
  ; sourceValidationReport =
      Replay.canonicalEmpiricalRuntimeValidationReport
  ; criteriaRows =
      canonicalAcceptanceCriteriaRows
  ; passingCriteria =
      canonicalPassingAcceptanceCriteria
  ; failingCriteria =
      canonicalFailingAcceptanceCriteria
  ; criterionCount =
      listCount canonicalAcceptanceCriteriaRows
  ; criterionCountMatches =
      refl
  ; passCount =
      listCount canonicalPassingAcceptanceCriteria
  ; passCountMatches =
      refl
  ; failCount =
      listCount canonicalFailingAcceptanceCriteria
  ; failCountMatches =
      refl
  ; deterministicReplayCriterionPasses =
      AcceptanceCriterionRow.passes runtimeCommandReproducibilityRow
  ; deterministicReplayCriterionPassesIsTrue =
      refl
  ; sourceChecksumCriterionPasses =
      AcceptanceCriterionRow.passes sourceChecksumMatchRow
  ; sourceChecksumCriterionPassesIsTrue =
      refl
  ; allExternalAuthorityCriteriaFail =
      true
  ; allExternalAuthorityCriteriaFailIsTrue =
      refl
  ; validationVerdictStillFails =
      Replay.canonicalValidationVerdictIsFail
  ; semanticAdequacyAccepted =
      Replay.EmpiricalRuntimeValidationReport.semanticAdequacyAccepted
        Replay.canonicalEmpiricalRuntimeValidationReport
  ; semanticAdequacyAcceptedIsFalse =
      Replay.EmpiricalRuntimeValidationReport.semanticAdequacyAcceptedIsFalse
        Replay.canonicalEmpiricalRuntimeValidationReport
  ; empiricalAdequacyAccepted =
      Replay.EmpiricalRuntimeValidationReport.empiricalAdequacyAccepted
        Replay.canonicalEmpiricalRuntimeValidationReport
  ; empiricalAdequacyAcceptedIsFalse =
      Replay.EmpiricalRuntimeValidationReport.empiricalAdequacyAcceptedIsFalse
        Replay.canonicalEmpiricalRuntimeValidationReport
  }

------------------------------------------------------------------------
-- Infrastructure/token summary for empirical runtime promotion gates.

record EmpiricalReplayInfrastructureTokenSummary : Setω where
  field
    summaryLabel : String
    sourceEvaluation : EmpiricalReplayAcceptanceEvaluation
    promotionGateRequirements :
      List Replay.EmpiricalRuntimePromotionGateRequirement
    populatedInfrastructureGates :
      List Replay.EmpiricalRuntimePromotionGateRequirement
    falseAcceptanceTokenGates :
      List Replay.EmpiricalRuntimePromotionGateRequirement
    promotionGateRequirementCount : Nat
    promotionGateRequirementCountMatches :
      promotionGateRequirementCount
      ≡
      listCount promotionGateRequirements
    populatedInfrastructureGateCount : Nat
    populatedInfrastructureGateCountMatches :
      populatedInfrastructureGateCount
      ≡
      listCount populatedInfrastructureGates
    falseAcceptanceTokenGateCount : Nat
    falseAcceptanceTokenGateCountMatches :
      falseAcceptanceTokenGateCount
      ≡
      listCount falseAcceptanceTokenGates
    providerAuthorityInfrastructurePopulated :
      Replay.EmpiricalRuntimePromotionGateRequirement.infrastructurePopulated
        Replay.canonicalProviderAuthorityGateRequirement
      ≡ true
    covariantChiSquareInfrastructurePopulated :
      Replay.EmpiricalRuntimePromotionGateRequirement.infrastructurePopulated
        Replay.canonicalCovariantChiSquareGateRequirement
      ≡ true
    covarianceCalibrationInfrastructurePopulated :
      Replay.EmpiricalRuntimePromotionGateRequirement.infrastructurePopulated
        Replay.canonicalCovarianceCalibrationGateRequirement
      ≡ true
    holdoutInfrastructurePopulated :
      Replay.EmpiricalRuntimePromotionGateRequirement.infrastructurePopulated
        Replay.canonicalHoldoutValidationGateRequirement
      ≡ true
    runtimeReplayInfrastructurePopulated :
      Replay.EmpiricalRuntimePromotionGateRequirement.infrastructurePopulated
        Replay.canonicalRuntimeReplayGateRequirement
      ≡ true
    replaySemanticAdequacyInfrastructurePopulated :
      Replay.EmpiricalRuntimePromotionGateRequirement.infrastructurePopulated
        Replay.canonicalReplaySemanticAdequacyGateRequirement
      ≡ true
    providerAuthorityAcceptanceTokenFalse :
      Replay.EmpiricalRuntimePromotionGateRequirement.acceptanceTokenPresent
        Replay.canonicalProviderAuthorityGateRequirement
      ≡ false
    covariantChiSquareAcceptanceTokenFalse :
      Replay.EmpiricalRuntimePromotionGateRequirement.acceptanceTokenPresent
        Replay.canonicalCovariantChiSquareGateRequirement
      ≡ false
    covarianceCalibrationAcceptanceTokenFalse :
      Replay.EmpiricalRuntimePromotionGateRequirement.acceptanceTokenPresent
        Replay.canonicalCovarianceCalibrationGateRequirement
      ≡ false
    holdoutAcceptanceTokenFalse :
      Replay.EmpiricalRuntimePromotionGateRequirement.acceptanceTokenPresent
        Replay.canonicalHoldoutValidationGateRequirement
      ≡ false
    runtimeReplayAuthorityTokenFalse :
      Replay.EmpiricalRuntimePromotionGateRequirement.acceptanceTokenPresent
        Replay.canonicalRuntimeReplayGateRequirement
      ≡ false
    replaySemanticAdequacyAcceptanceTokenFalse :
      Replay.EmpiricalRuntimePromotionGateRequirement.acceptanceTokenPresent
        Replay.canonicalReplaySemanticAdequacyGateRequirement
      ≡ false

open EmpiricalReplayInfrastructureTokenSummary public

canonicalEmpiricalReplayInfrastructureTokenSummary :
  EmpiricalReplayInfrastructureTokenSummary
canonicalEmpiricalReplayInfrastructureTokenSummary = record
  { summaryLabel =
      "populated empirical runtime infrastructure with false promotion tokens"
  ; sourceEvaluation =
      canonicalEmpiricalReplayAcceptanceEvaluation
  ; promotionGateRequirements =
      Replay.canonicalEmpiricalRuntimePromotionGateRequirements
  ; populatedInfrastructureGates =
      Replay.canonicalPopulatedInfrastructureGateRequirements
  ; falseAcceptanceTokenGates =
      Replay.canonicalFalseAcceptanceTokenGateRequirements
  ; promotionGateRequirementCount =
      listCount Replay.canonicalEmpiricalRuntimePromotionGateRequirements
  ; promotionGateRequirementCountMatches =
      refl
  ; populatedInfrastructureGateCount =
      listCount Replay.canonicalPopulatedInfrastructureGateRequirements
  ; populatedInfrastructureGateCountMatches =
      refl
  ; falseAcceptanceTokenGateCount =
      listCount Replay.canonicalFalseAcceptanceTokenGateRequirements
  ; falseAcceptanceTokenGateCountMatches =
      refl
  ; providerAuthorityInfrastructurePopulated =
      Replay.canonicalProviderAuthorityGateInfrastructurePopulated
  ; covariantChiSquareInfrastructurePopulated =
      Replay.canonicalCovariantChiSquareGateInfrastructurePopulated
  ; covarianceCalibrationInfrastructurePopulated =
      Replay.canonicalCovarianceCalibrationGateInfrastructurePopulated
  ; holdoutInfrastructurePopulated =
      Replay.canonicalHoldoutValidationGateInfrastructurePopulated
  ; runtimeReplayInfrastructurePopulated =
      Replay.canonicalRuntimeReplayGateInfrastructurePopulated
  ; replaySemanticAdequacyInfrastructurePopulated =
      Replay.canonicalReplaySemanticAdequacyGateInfrastructurePopulated
  ; providerAuthorityAcceptanceTokenFalse =
      Replay.canonicalProviderAuthorityGateAcceptanceTokenIsFalse
  ; covariantChiSquareAcceptanceTokenFalse =
      Replay.canonicalCovariantChiSquareGateAcceptanceTokenIsFalse
  ; covarianceCalibrationAcceptanceTokenFalse =
      Replay.canonicalCovarianceCalibrationGateAcceptanceTokenIsFalse
  ; holdoutAcceptanceTokenFalse =
      Replay.canonicalHoldoutValidationGateAcceptanceTokenIsFalse
  ; runtimeReplayAuthorityTokenFalse =
      Replay.canonicalRuntimeReplayGateAcceptanceTokenIsFalse
  ; replaySemanticAdequacyAcceptanceTokenFalse =
      Replay.canonicalReplaySemanticAdequacyGateAcceptanceTokenIsFalse
  }

------------------------------------------------------------------------
-- Exact counts and guard lemmas.

canonicalAcceptanceCriterionCountIs10 :
  EmpiricalReplayAcceptanceEvaluation.criterionCount
    canonicalEmpiricalReplayAcceptanceEvaluation
  ≡ 10
canonicalAcceptanceCriterionCountIs10 = refl

canonicalAcceptancePassCountIs2 :
  EmpiricalReplayAcceptanceEvaluation.passCount
    canonicalEmpiricalReplayAcceptanceEvaluation
  ≡ 2
canonicalAcceptancePassCountIs2 = refl

canonicalAcceptanceFailCountIs8 :
  EmpiricalReplayAcceptanceEvaluation.failCount
    canonicalEmpiricalReplayAcceptanceEvaluation
  ≡ 8
canonicalAcceptanceFailCountIs8 = refl

canonicalReplayPromotionGateRequirementCountIs6 :
  EmpiricalReplayInfrastructureTokenSummary.promotionGateRequirementCount
    canonicalEmpiricalReplayInfrastructureTokenSummary
  ≡ 6
canonicalReplayPromotionGateRequirementCountIs6 = refl

canonicalReplayPopulatedInfrastructureGateCountIs6 :
  EmpiricalReplayInfrastructureTokenSummary.populatedInfrastructureGateCount
    canonicalEmpiricalReplayInfrastructureTokenSummary
  ≡ 6
canonicalReplayPopulatedInfrastructureGateCountIs6 = refl

canonicalReplayFalseAcceptanceTokenGateCountIs6 :
  EmpiricalReplayInfrastructureTokenSummary.falseAcceptanceTokenGateCount
    canonicalEmpiricalReplayInfrastructureTokenSummary
  ≡ 6
canonicalReplayFalseAcceptanceTokenGateCountIs6 = refl

canonicalDeterministicReplayCriterionPasses :
  AcceptanceCriterionRow.passes runtimeCommandReproducibilityRow
  ≡ true
canonicalDeterministicReplayCriterionPasses = refl

canonicalSourceChecksumCriterionPasses :
  AcceptanceCriterionRow.passes sourceChecksumMatchRow
  ≡ true
canonicalSourceChecksumCriterionPasses = refl

canonicalProviderAuthorityTokenCriterionFails :
  AcceptanceCriterionRow.failsOrMissing providerAuthorityTokenRow
  ≡ true
canonicalProviderAuthorityTokenCriterionFails = refl

canonicalObservableDefinitionAcceptanceCriterionFails :
  AcceptanceCriterionRow.failsOrMissing observableDefinitionAcceptanceRow
  ≡ true
canonicalObservableDefinitionAcceptanceCriterionFails = refl

canonicalProjectionTransformLawCriterionFails :
  AcceptanceCriterionRow.failsOrMissing projectionTransformLawRow
  ≡ true
canonicalProjectionTransformLawCriterionFails = refl

canonicalComparisonLawAcceptanceCriterionFails :
  AcceptanceCriterionRow.failsOrMissing comparisonLawAcceptanceRow
  ≡ true
canonicalComparisonLawAcceptanceCriterionFails = refl

canonicalCovarianceUnitCalibrationCriterionFails :
  AcceptanceCriterionRow.failsOrMissing covarianceUnitCalibrationRow
  ≡ true
canonicalCovarianceUnitCalibrationCriterionFails = refl

canonicalHoldoutProtocolPassCriterionFails :
  AcceptanceCriterionRow.failsOrMissing holdoutProtocolPassRow
  ≡ true
canonicalHoldoutProtocolPassCriterionFails = refl

canonicalParserReducerVersionPinCriterionFails :
  AcceptanceCriterionRow.failsOrMissing parserReducerVersionPinRow
  ≡ true
canonicalParserReducerVersionPinCriterionFails = refl

canonicalSemanticReviewAcceptanceCriterionFails :
  AcceptanceCriterionRow.failsOrMissing semanticReviewAcceptanceRow
  ≡ true
canonicalSemanticReviewAcceptanceCriterionFails = refl

canonicalReplayAcceptanceSemanticAdequacyAcceptedIsFalse :
  EmpiricalReplayAcceptanceEvaluation.semanticAdequacyAccepted
    canonicalEmpiricalReplayAcceptanceEvaluation
  ≡ false
canonicalReplayAcceptanceSemanticAdequacyAcceptedIsFalse =
  EmpiricalReplayAcceptanceEvaluation.semanticAdequacyAcceptedIsFalse
    canonicalEmpiricalReplayAcceptanceEvaluation

canonicalReplayAcceptanceEmpiricalAdequacyAcceptedIsFalse :
  EmpiricalReplayAcceptanceEvaluation.empiricalAdequacyAccepted
    canonicalEmpiricalReplayAcceptanceEvaluation
  ≡ false
canonicalReplayAcceptanceEmpiricalAdequacyAcceptedIsFalse =
  EmpiricalReplayAcceptanceEvaluation.empiricalAdequacyAcceptedIsFalse
    canonicalEmpiricalReplayAcceptanceEvaluation
