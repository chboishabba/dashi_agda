module DASHI.Core.ProofExperimentAction369IntegrationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.HistoryIndexedProofExperimentActionLoopExact as Loop
import DASHI.Moonshine.Base369OODAProofExperimentObserverExact as O369
import DASHI.Moonshine.Monster196830RegularBulkResidualControlPatternExact as Bulk

------------------------------------------------------------------------
-- INTEGRATION OWNER
--
-- The same live residual fibre supports:
--   * proof search (think),
--   * information acquisition (look),
--   * physical/relational experiment (test),
--   * admitted physical transition (act).
-- Base369 charts the control role; the 196830/53 arithmetic supplies only an
-- optional regular-bulk/residual design-pattern receipt.
------------------------------------------------------------------------

record IntegratedCyberneticPoint : Set₁ where
  constructor integrated-cybernetic-point
  field
    fibre : Loop.LiveResidualFibre
    phase : Loop.OODAPhase
    phaseChart : O369.OODA369Chart
    chartMatchesPhase : O369.phase phaseChart ≡ phase
    regularResidualReference : String
    proofSearchReference : String
    experimentDesignReference : String
    actionabilityReference : String
    authorityReference : String
    executionReference : String

open IntegratedCyberneticPoint public

record BranchResidualAssessment : Set₁ where
  constructor branch-residual-assessment
  field
    branchReference : String
    proofObligationReference : String
    unresolvedResidualReference : String
    assumptionReference : String
    immediate3Reference : String
    medium6Reference : String
    long9Reference : String

open BranchResidualAssessment public

record ProofQualifiedBranch : Set₁ where
  constructor proof-qualified-branch
  field
    source : Loop.LiveResidualFibre
    candidate : Loop.CandidateMove source
    assessment : BranchResidualAssessment
    admissibilityReference : String
    authorityReference : String
    mayExecuteReference : String

open ProofQualifiedBranch public

------------------------------------------------------------------------
-- A branch can be operationally executable while retaining unresolved semantic
-- or long-horizon residuals.  Conversely, a well-scored or elegant branch has
-- no execution capability without the separate admissibility/authority lane.
------------------------------------------------------------------------

record BranchComparison : Set₁ where
  constructor branch-comparison
  field
    left right : ProofQualifiedBranch
    valueComparisonReference : String
    residualComparisonReference : String
    worstCaseReference : String
    consumerAdequacyReference : String
    selectedReference : String

open BranchComparison public

------------------------------------------------------------------------
-- Canonical scale receipt is imported, not reinterpreted.
------------------------------------------------------------------------

canonical196830Plus53Receipt : Bulk.BulkResidualScaleReceipt
canonical196830Plus53Receipt = Bulk.canonicalBulkResidualScaleReceipt

record IntegratedCyberneticBoundary : Set where
  constructor integrated-cybernetic-boundary
  field
    highPostEntropyScoreAuthorisesExecution : Bool
    highPostEntropyScoreAuthorisesExecutionIsFalse :
      highPostEntropyScoreAuthorisesExecution ≡ false

    proofSearchClosureImpliesPhysicalSuccess : Bool
    proofSearchClosureImpliesPhysicalSuccessIsFalse :
      proofSearchClosureImpliesPhysicalSuccess ≡ false

    physicalSuccessImpliesLongHorizonBenefit : Bool
    physicalSuccessImpliesLongHorizonBenefitIsFalse :
      physicalSuccessImpliesLongHorizonBenefit ≡ false

    same369SectorImpliesSameUnderlyingState : Bool
    same369SectorImpliesSameUnderlyingStateIsFalse :
      same369SectorImpliesSameUnderlyingState ≡ false

    bulkResidualArithmeticDeterminesRuntimeCardinality : Bool
    bulkResidualArithmeticDeterminesRuntimeCardinalityIsFalse :
      bulkResidualArithmeticDeterminesRuntimeCardinality ≡ false

canonicalIntegratedCyberneticBoundary : IntegratedCyberneticBoundary
canonicalIntegratedCyberneticBoundary =
  integrated-cybernetic-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
