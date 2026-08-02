module DASHI.Physics.YangMills.BalabanClayGate4FiniteWeightedSchurCertificateCompletionExact where

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (Dec; yes; no; Empty)

import DASHI.Physics.YangMills.BalabanClayGate4FiniteWeightedSchurCertificateExact as Base

------------------------------------------------------------------------
-- Total executable weighted-Schur certificate decision.
--
-- Issai Schur,
-- "Bemerkungen zur Theorie der beschränkten Bilinearformen mit unendlich
-- vielen Veränderlichen", Journal für die reine und angewandte Mathematik 140
-- (1911), 1--28. No DOI recorded.
--
-- The earlier module exposed separate row and column decisions.  This module
-- combines them into one `Dec` for the full accepted certificate and proves
-- that either branch is logically complete.  Therefore an exact rational or
-- outward-rounded interval implementation can run one checker and obtain the
-- universal row and column theorems without any manually assembled receipt.
------------------------------------------------------------------------

data DecidedCertificate (P : Set₁) : Set₁ where
  certificateAccepted : P → DecidedCertificate P
  certificateRefuted : (P → Empty) → DecidedCertificate P

checkFiniteWeightedSchurCertificate :
  ∀ {Input Output Scalar}
    (dataSet : Base.FiniteWeightedComparisonData Input Output Scalar) →
  DecidedCertificate (Base.AcceptedFiniteWeightedCertificate dataSet)
checkFiniteWeightedSchurCertificate dataSet
  with Base.checkAllWeightedRows dataSet
     | Base.checkAllWeightedColumns dataSet
... | yes rows | yes columns = certificateAccepted record
      { allRowsAccepted = rows
      ; allColumnsAccepted = columns
      }
... | no rowsRefuted | columnsDecision =
      certificateRefuted (λ certificate →
        rowsRefuted (Base.allRowsAccepted certificate))
... | yes rows | no columnsRefuted =
      certificateRefuted (λ certificate →
        columnsRefuted (Base.allColumnsAccepted certificate))

record ExecutedFiniteWeightedSchurCertificate
    {Input Output Scalar}
    (dataSet : Base.FiniteWeightedComparisonData Input Output Scalar) : Set₁ where
  field
    accepted : Base.AcceptedFiniteWeightedCertificate dataSet

open ExecutedFiniteWeightedSchurCertificate public

executeAcceptedCertificate :
  ∀ {Input Output Scalar}
    {dataSet : Base.FiniteWeightedComparisonData Input Output Scalar} →
  ExecutedFiniteWeightedSchurCertificate dataSet →
  Base.AcceptedFiniteWeightedCertificate dataSet
executeAcceptedCertificate = accepted

executedRowBoundEverywhere :
  ∀ {Input Output Scalar}
    {dataSet : Base.FiniteWeightedComparisonData Input Output Scalar} →
  ExecutedFiniteWeightedSchurCertificate dataSet →
  ∀ output → Base.RowBound dataSet output
executedRowBoundEverywhere execution =
  Base.acceptedRowBoundEverywhere (accepted execution)

executedColumnBoundEverywhere :
  ∀ {Input Output Scalar}
    {dataSet : Base.FiniteWeightedComparisonData Input Output Scalar} →
  ExecutedFiniteWeightedSchurCertificate dataSet →
  ∀ input → Base.ColumnBound dataSet input
executedColumnBoundEverywhere execution =
  Base.acceptedColumnBoundEverywhere (accepted execution)

finiteWeightedCertificateTotalDecisionLevel : ProofLevel
finiteWeightedCertificateTotalDecisionLevel = machineChecked

finiteWeightedCertificateFailureRefutationLevel : ProofLevel
finiteWeightedCertificateFailureRefutationLevel = machineChecked

finiteWeightedCertificateUniversalExecutionLevel : ProofLevel
finiteWeightedCertificateUniversalExecutionLevel = machineChecked
