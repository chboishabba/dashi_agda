module DASHI.Mathematics.Algebra.RationalAlbertF4ExactWeightDecompositionReceiptExact where

------------------------------------------------------------------------
-- EXACT Q(i) WEIGHT-SPACE DECOMPOSITION OF THE ALBERT DERIVATION ALGEBRA
--
-- Companion producer:
--   scripts/albert_f4_exact_weight_probe.py
--
-- Starting from the same exact 52-dimensional inner-derivation basis and the
-- four explicit commuting Cartan derivations selected in
-- `RationalAlbertF4CartanRootReceiptExact`, the producer represents every
-- adjoint Cartan operator exactly over Q and applies symbolic spectral
-- projectors over Q(i).  It proves computationally, without floating point:
--
--   zero joint weight:     rank 4;
--   D4 sector:             24 one-dimensional root spaces;
--   vector sector:          8 one-dimensional weight/root spaces;
--   positive half-spin:     8 one-dimensional weight/root spaces;
--   negative half-spin:     8 one-dimensional weight/root spaces.
--
-- Hence the complexified root-space ledger is exactly
--
--   4 + 24 + 8 + 8 + 8 = 52,
--
-- with 48 nonzero one-dimensional root spaces and the same triality partition
-- as the independent standard F4 root datum on companion Lean.
--
-- This is an exact symbolic executable receipt.  It is deliberately kept
-- separate from an Agda-internal scalar-extension/projector proof and from the
-- standard classification theorem identifying the resulting Lie algebra as F4.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record ExactWeightSpaceReceipt : Set where
  constructor exact-weight-space-receipt
  field
    scriptPath : String
    scalarExtension : String
    floatingPointUsed : Bool
    CartanDimension : Nat
    zeroWeightDimension : Nat
    d4RootSpaceCount : Nat
    d4EachRootSpaceDimension : Nat
    vectorWeightSpaceCount : Nat
    vectorEachWeightSpaceDimension : Nat
    spinPlusWeightSpaceCount : Nat
    spinPlusEachWeightSpaceDimension : Nat
    spinMinusWeightSpaceCount : Nat
    spinMinusEachWeightSpaceDimension : Nat
    totalNonzeroRootSpaces : Nat
    totalDimension : Nat
    exactSymbolicProjectorsUsed : Bool
open ExactWeightSpaceReceipt public

canonicalExactWeightSpaceReceipt : ExactWeightSpaceReceipt
canonicalExactWeightSpaceReceipt =
  exact-weight-space-receipt
    "scripts/albert_f4_exact_weight_probe.py"
    "Q(i)"
    false
    4
    4
    24 1
    8 1
    8 1
    8 1
    48
    52
    true

record CrossKernelRootMatchReceipt : Set where
  constructor cross-kernel-root-match-receipt
  field
    companionLeanRootCount48 : Nat
    companionLeanLongRootCount24 : Nat
    companionLeanShortRootCount24 : Nat
    companionLeanVectorSectorCount8 : Nat
    companionLeanSpinPlusSectorCount8 : Nat
    companionLeanSpinMinusSectorCount8 : Nat
    companionLeanF4CartanPaid : Bool
    companionLeanWeylOrder1152Paid : Bool
    exactAlbertWeightLabelsMatchTrialityLedger : Bool
    literalEigenvectorToLeanRootBijectionKernelPaid : Bool
open CrossKernelRootMatchReceipt public

canonicalCrossKernelRootMatchReceipt : CrossKernelRootMatchReceipt
canonicalCrossKernelRootMatchReceipt =
  cross-kernel-root-match-receipt
    48 24 24 8 8 8 true true true false

record Boundary : Set where
  constructor boundary
  field
    exactQIRootSpaceDecompositionPaidByProducer : Bool
    zeroWeightRankFourPaidByProducer : Bool
    fortyEightOneDimensionalNonzeroRootSpacesPaidByProducer : Bool
    exactTrialityRootPartitionPaidByProducer : Bool
    floatingRootExtractionStillNeeded : Bool
    AgdaScalarExtensionReplayPaid : Bool
    AgdaRootProjectorReplayPaid : Bool
    sameLieAlgebraF4ClassificationPaid : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary =
  boundary true true true true false false false false
