module DASHI.Foundations.AlbertJordanExternalDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- EXTERNAL ALBERT/JORDAN DONOR RECEIPT
--
-- External source:
--   Cobord/JordanAlgebra
--   commit a4b0d58554732ced63b4217200baa56be5a2c3d5
--   Lean 4.31.0 / mathlib 4.31.0
--
-- The companion Lean branch pins this repository as a git submodule and audits
-- its exact source surface.  This Agda owner does not import Lean proof
-- authority.  It records only the cross-prover artifact/provenance boundary.
------------------------------------------------------------------------

record AlbertExternalDonorReceipt : Set where
  constructor albert-external-donor-receipt
  field
    repository : String
    commit : String
    leanToolchain : String
    mathlibRevision : String

    h3OctonionicCarrierSourceWritten : Bool
    linearAlbertEquivSourceWritten : Bool
    jordanIdentityProducerSourceWritten : Bool
    traceSourceWritten : Bool
    traceOneIsThreeSourceWritten : Bool
    cubicDeterminantSourceWritten : Bool
    cubicHomogeneitySourceWritten : Bool
    determinantOneSourceWritten : Bool
    rankThreeDetTraceSourceWritten : Bool

    fullCubicIdentitiesSourceWritten : Bool
    e6RepresentationSourceWritten : Bool
    f4AutomorphismRecognitionSourceWritten : Bool
    exactLeanKernelReceiptObservedHere : Bool
open AlbertExternalDonorReceipt public

pinnedAlbertDonor : AlbertExternalDonorReceipt
pinnedAlbertDonor = albert-external-donor-receipt
  "https://github.com/Cobord/JordanAlgebra"
  "a4b0d58554732ced63b4217200baa56be5a2c3d5"
  "leanprover/lean4:v4.31.0"
  "v4.31.0"
  true true true true true true true true true
  false false false false

record DonorCompatibilityBoundary : Set where
  constructor donor-compatibility-boundary
  field
    donorToolchainDiffersFromDashi : Bool
    donorSourceCopiedIntoAgda : Bool
    donorSourceCopiedIntoDashiLeanNamespace : Bool
    sameKernelDashiInstantiationPaid : Bool
    donorLicenseDeclaredByGitHubMetadata : Bool
open DonorCompatibilityBoundary public

canonicalDonorCompatibilityBoundary : DonorCompatibilityBoundary
canonicalDonorCompatibilityBoundary = donor-compatibility-boundary
  true false false false false
