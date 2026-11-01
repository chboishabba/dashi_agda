module DASHI.Physics.YangMills.YangMillsSubmissionRound7Ledger where

open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (ℕ)

import DASHI.Physics.YangMills.YangMillsSubmissionObligationCardinalityExact as Counts
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Round-seven ledger: exact submission inventory plus three active reduction
-- fronts.  Status is intentionally finer than a Boolean closure flag.
------------------------------------------------------------------------

data SubmissionGroupStatus : Set where
  definitionClosed : SubmissionGroupStatus
  ownedReducerAvailable : SubmissionGroupStatus
  physicalInputsConditional : SubmissionGroupStatus
  publishedImportBoundary : SubmissionGroupStatus
  openAnalyticFrontier : SubmissionGroupStatus
  externalAuditGate : SubmissionGroupStatus

record SubmissionRound7Ledger : Set₁ where
  field
    theoremSpineCount : ℕ
    fullSubmissionCount : ℕ

    gate4Status : SubmissionGroupStatus
    p06GraphKernelStatus : SubmissionGroupStatus
    p06ModelLeafStatus : SubmissionGroupStatus
    p11ReductionStatus : SubmissionGroupStatus
    bishopHalfBallStatus : SubmissionGroupStatus
    rgTransferStatus : SubmissionGroupStatus
    thermodynamicContinuumStatus : SubmissionGroupStatus
    osEndpointStatus : SubmissionGroupStatus
    foundationStatus : SubmissionGroupStatus
    gaugeStructureStatus : SubmissionGroupStatus
    auditStatus : SubmissionGroupStatus

    boundary : String

open SubmissionRound7Ledger public

currentSubmissionRound7Ledger : SubmissionRound7Ledger
currentSubmissionRound7Ledger = record
  { theoremSpineCount = Counts.theoremSpineObligationCount
  ; fullSubmissionCount = Counts.fullSubmissionObligationCount
  ; gate4Status = physicalInputsConditional
  ; p06GraphKernelStatus = ownedReducerAvailable
  ; p06ModelLeafStatus = openAnalyticFrontier
  ; p11ReductionStatus = ownedReducerAvailable
  ; bishopHalfBallStatus = ownedReducerAvailable
  ; rgTransferStatus = publishedImportBoundary
  ; thermodynamicContinuumStatus = openAnalyticFrontier
  ; osEndpointStatus = publishedImportBoundary
  ; foundationStatus = physicalInputsConditional
  ; gaugeStructureStatus = openAnalyticFrontier
  ; auditStatus = externalAuditGate
  ; boundary =
      "Round seven formalises all 191 theorem-spine obligations and all 219 A-I submission obligations, packages five owned P06 graph consequences, reduces P11 absorption to a uniform p0 lower bound plus one scalar payment, derives the Bishop half-ball square estimate from a concrete order kernel, and replaces string endpoint placeholders with typed theorem interfaces. No uninhabited analytic field is promoted."
  }

submissionRound7LedgerLevel : ProofLevel
submissionRound7LedgerLevel = machineChecked
