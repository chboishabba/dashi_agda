module DASHI.Reasoning.AlbertF4TauCetiFormalDonorReceiptExact where

------------------------------------------------------------------------
-- EXTERNAL FORMAL-DONOR AUDIT RECEIPT
--
-- External repository: TauCetiProject/TauCeti
-- Pinned audited commit: b160c8a8f870997b9652251aefd5e64b8c9a72ef
-- License/provenance: Apache-2.0 / Tau Ceti authorship retained.
--
-- At this current-main pin the external repository contains substantial formal
-- Albert-algebra infrastructure and canonical F4 Lie/root-datum/Chevalley
-- infrastructure.  Its Albert derivation owner now additionally proves:
--
--   * the trace-zero Albert subspace J0 is a Lie submodule for Der J;
--   * finrank J0 = 26 under the donor's stated rank hypotheses;
--   * Der J acts faithfully on J0.
--
-- Tau Ceti's own file still presents `F4 = Der H3(O)` as the intended endpoint.
-- A current repository search did not locate a same-object Lie equivalence from
-- the Albert derivation algebra to its canonical F4 Lie algebra, nor an
-- Albert-automorphism/F4 group theorem.
--
-- This owner records the donor inventory and the missing morphism only.  It
-- does not import external proof authority and does not turn donor inventory,
-- names, dimensions, faithful 26-actions or root tables into a DASHI theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

record FormalDonorReceipt : Set where
  constructor formal-donor-receipt
  field
    repository : String
    pinnedCommit : String
    license : String
    albertBasicOwner : String
    albertDerivationOwner : String
    f4RootDatumOwner : String
    f4LieStack : String
    albertStackLocated : Bool
    albertTraceZeroLieSubmoduleLocated : Bool
    albertTraceZeroFinrank26Located : Bool
    albertTraceZeroFaithfulActionLocated : Bool
    canonicalF4StackLocated : Bool
    sameObjectAlbertDerivationToF4LieEquivLocated : Bool
    sameObjectAlbertAutToF4GroupLocated : Bool
    donorInventoryCreatesNativeClassification : Bool
    externalFormalAuthorityImportedIntoAgda : Bool
open FormalDonorReceipt public

canonicalReceipt : FormalDonorReceipt
canonicalReceipt = formal-donor-receipt
  "TauCetiProject/TauCeti"
  "b160c8a8f870997b9652251aefd5e64b8c9a72ef"
  "Apache-2.0"
  "TauCeti/Algebra/AlbertAlgebra/Basic.lean"
  "TauCeti/Algebra/AlbertAlgebra/Derivation.lean"
  "TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/F4/Basic.lean"
  "TauCeti/Algebra/Lie/F4/..."
  true true true true true false false false false

record Boundary : Set where
  constructor boundary
  field
    tauCetiAlbertStackLocated : Bool
    tauCetiTraceZeroTwentySixRepresentationLocated : Bool
    tauCetiTraceZeroFaithfulActionLocated : Bool
    tauCetiCanonicalF4StackLocated : Bool
    sameObjectAlbertToCanonicalF4BridgeLocated : Bool
    sameObjectAlbertAutToF4GroupLocated : Bool
    donorInventoryCreatesNativeClassification : Bool
    faithfulTwentySixCreatesNativeClassification : Bool
    sourceAuthorshipPreserved : Bool
    externalFormalAuthorityImportedIntoAgda : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  canonicalReceipt.albertStackLocated
  canonicalReceipt.albertTraceZeroFinrank26Located
  canonicalReceipt.albertTraceZeroFaithfulActionLocated
  canonicalReceipt.canonicalF4StackLocated
  canonicalReceipt.sameObjectAlbertDerivationToF4LieEquivLocated
  canonicalReceipt.sameObjectAlbertAutToF4GroupLocated
  canonicalReceipt.donorInventoryCreatesNativeClassification
  false
  true
  canonicalReceipt.externalFormalAuthorityImportedIntoAgda
