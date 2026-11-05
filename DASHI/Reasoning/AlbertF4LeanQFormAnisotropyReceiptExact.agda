module DASHI.Reasoning.AlbertF4LeanQFormAnisotropyReceiptExact where

------------------------------------------------------------------------
-- CROSS-PROVER RECEIPT ONLY
--
-- Companion Lean PR #52 source-writes, on its literal rational octonion
-- carrier:
--
-- * the positive eight-square norm is anisotropic over Q;
-- * norm multiplicativity + anisotropy imply no zero divisors;
-- * the exact 4+48 F4 root-space producer is explicitly a Q(i) scalar-
--   extension/splitting chart and is not an original-Q-form classification.
--
-- This Agda owner records those source-status facts only.  It does not import
-- Lean kernel proof authority and it does not promote cross-prover receipts into
-- Agda theorems about the native Agda Albert carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

record LeanQFormReceipt : Set where
  constructor lean-q-form-receipt
  field
    leanRepository : String
    leanPR : String
    anisotropyOwner : String
    scalarExtensionOwner : String
    nativeQOctonionNormAnisotropySourceWritten : Bool
    nativeQOctonionNoZeroDivisorsSourceWritten : Bool
    qiRootChartRecordedAsScalarExtensionData : Bool
    qiRootChartClassifiesOriginalQForm : Bool
    sameActionUnitStabilizerJordanPaidInLean : Bool
    leanKernelProofAuthorityImportedIntoAgda : Bool
open LeanQFormReceipt public

canonicalReceipt : LeanQFormReceipt
canonicalReceipt = lean-q-form-receipt
  "chboishabba/dashi_lean4"
  "#52"
  "Integration/RationalOctonionDivisionNorm.lean"
  "Integration/RationalAlbertF4ScalarExtensionFormBoundary.lean"
  true true true false true false

record Boundary : Set where
  constructor boundary
  field
    leanNativeQOctonionNormAnisotropySourceWritten : Bool
    leanNativeQOctonionNoZeroDivisorsSourceWritten : Bool
    qiRootChartRecordedAsScalarExtensionData : Bool
    qiRootChartClassifiesOriginalQForm : Bool
    sameActionStructuralStabilizerPaidInLean : Bool
    leanKernelProofAuthorityImportedIntoAgda : Bool
    originalQFormGroupClassificationPaid : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  canonicalReceipt.nativeQOctonionNormAnisotropySourceWritten
  canonicalReceipt.nativeQOctonionNoZeroDivisorsSourceWritten
  canonicalReceipt.qiRootChartRecordedAsScalarExtensionData
  canonicalReceipt.qiRootChartClassifiesOriginalQForm
  canonicalReceipt.sameActionUnitStabilizerJordanPaidInLean
  canonicalReceipt.leanKernelProofAuthorityImportedIntoAgda
  false
