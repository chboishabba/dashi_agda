module DASHI.Reasoning.AlbertF4TauCetiFormalDonorReceiptExact where

------------------------------------------------------------------------
-- EXTERNAL FORMAL-DONOR AUDIT RECEIPT
--
-- External repository: TauCetiProject/TauCeti
-- Pinned audited commit: 85ed0984159b8de1ed8c11541105bb1d89c787e4
-- License/provenance: Apache-2.0 / Tau Ceti authorship retained.
--
-- At the pinned commit the external repository contains substantial formal
-- Albert-algebra infrastructure and substantial canonical F4 Lie/root-datum/
-- Chevalley infrastructure.  Repository search did not locate a same-object
-- theorem identifying its Albert derivation algebra with its canonical F4 Lie
-- algebra, nor an Albert-automorphism/F4 group theorem.
--
-- This owner records the donor inventory and the missing morphism only.  It
-- does not import external proof authority and does not turn donor inventory,
-- names, dimensions or root tables into a DASHI theorem.
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
    canonicalF4StackLocated : Bool
    sameObjectAlbertDerivationToF4LieEquivLocated : Bool
    sameObjectAlbertAutToF4GroupLocated : Bool
    donorInventoryCreatesNativeClassification : Bool
    externalFormalAuthorityImportedIntoAgda : Bool
open FormalDonorReceipt public

canonicalReceipt : FormalDonorReceipt
canonicalReceipt = formal-donor-receipt
  "TauCetiProject/TauCeti"
  "85ed0984159b8de1ed8c11541105bb1d89c787e4"
  "Apache-2.0"
  "TauCeti/Algebra/AlbertAlgebra/Basic.lean"
  "TauCeti/Algebra/AlbertAlgebra/Derivation.lean"
  "TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/F4/Basic.lean"
  "TauCeti/Algebra/Lie/F4/..."
  true true false false false false

record Boundary : Set where
  constructor boundary
  field
    tauCetiAlbertStackLocated : Bool
    tauCetiCanonicalF4StackLocated : Bool
    sameObjectAlbertToCanonicalF4BridgeLocated : Bool
    sameObjectAlbertAutToF4GroupLocated : Bool
    donorInventoryCreatesNativeClassification : Bool
    sourceAuthorshipPreserved : Bool
    externalFormalAuthorityImportedIntoAgda : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  canonicalReceipt.albertStackLocated
  canonicalReceipt.canonicalF4StackLocated
  canonicalReceipt.sameObjectAlbertDerivationToF4LieEquivLocated
  canonicalReceipt.sameObjectAlbertAutToF4GroupLocated
  canonicalReceipt.donorInventoryCreatesNativeClassification
  true
  canonicalReceipt.externalFormalAuthorityImportedIntoAgda
