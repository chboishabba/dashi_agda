module DASHI.Biology.DrosophilaGautheyDepositRecoveryNoGoExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Closed-world deposit audit for the pooled conventional-2p identity carrier.
--
-- Scientific source:
-- Wayan Gauthey; Albert Lin; Osama M. Ahmed; Andrew M. Leifer; Mala Murthy;
-- Stephan Y. Thiberge, "High-speed whole-brain imaging in Drosophila",
-- DOI 10.1038/s41467-026-72437-1;
-- preprocessed data DOI 10.5281/zenodo.17618684;
-- analysis code github:murthylab/lightbead-analysis.
--
-- Runtime audit of the complete Data.zip central directory found 35 members.
-- None of the eight source-code-declared conventional-2p generating inputs
-- (four GCaMP6f trial pickles + four n1000 label files) is deposited there.
-- Thus the conditional exact-trace recovery route is closed-negative for this
-- deposit. This does not prove the scientific identities do not exist; it means
-- they must be supplied by an external scientific producer/receipt.
------------------------------------------------------------------------

record DepositRecoveryAudit : Set where
  constructor depositRecoveryAudit
  field
    archiveMemberCount : Nat
    requiredGeneratingFileCount : Nat
    uniquelyResolvedGeneratingFileCount : Nat
    zeroMatchGeneratingFileCount : Nat
    ambiguousGeneratingFileCount : Nat
    allRequiredUniquelyResolved : Bool
    exactTraceRecoveryAvailableFromDeposit : Bool
    externalScientificReceiptRequired : Bool
    requiredSelectedROIRows : Nat

open DepositRecoveryAudit public

canonicalDepositRecoveryAudit : DepositRecoveryAudit
canonicalDepositRecoveryAudit =
  depositRecoveryAudit
    35
    8
    0
    8
    0
    false
    false
    true
    940

record DepositRecoveryBoundary : Set where
  constructor depositRecoveryBoundary
  field
    missingGeneratingInputsBlocksExactRecovery : Bool
    pooledSelectedMatrixDoesNotReconstructMissingSourceRows : Bool
    sourceCodeDescriptionDoesNotManufactureAbsentArtifact : Bool
    closedWorldNoGoDoesNotMeanScientificIdentityImpossible : Bool
    externalReceiptMustCoverAllSelectedRows : Bool
    externalReceiptStillDoesNotImplyMaleCNSNeuronIdentity : Bool

open DepositRecoveryBoundary public

canonicalDepositRecoveryBoundary : DepositRecoveryBoundary
canonicalDepositRecoveryBoundary =
  depositRecoveryBoundary true true true true true true

paymentAProducerKind : String
paymentAProducerKind =
  "external 940-row selected_roi -> (trial, plane, cluster) scientific receipt"
