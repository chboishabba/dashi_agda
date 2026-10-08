module DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoExecutionBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

record ExecutionReceiptBoundary : Set where
  constructor execution-receipt-boundary
  field
    sourceFilesCommitted : Bool
    umbrellaImportCommitted : Bool
    exactHeadAgdaReceiptPresent : Bool
    exactHeadBlochRuntimeReceiptPresent : Bool
    independentBNSAuditReceiptPresent : Bool
    rawARPESIngestReceiptPresent : Bool

canonicalExecutionReceiptBoundary : ExecutionReceiptBoundary
canonicalExecutionReceiptBoundary =
  execution-receipt-boundary true true false false false false
