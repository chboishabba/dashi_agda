module DASHI.Interop.SLRGWBSourceRoleAttachmentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRGWBClaimRelativeSourceRoleAtlasExact as Atlas
import DASHI.Interop.SLRGWBWikimediaIdentityResidualContractionExact as Identity

------------------------------------------------------------------------
-- GWB CLAIM-RELATIVE SOURCE ROLE ATTACHMENT
--
-- Runtime:
--   tools/slr-discourse-reconstruct/slr_gwb_source_role_attachment.py
--   tools/slr-discourse-reconstruct/run_gwb_source_role_attachment.sh
--
-- Roles attach to document provenance.  They constrain downstream claim/evidence
-- consumers but do not manufacture source identity, event truth, or authority.
------------------------------------------------------------------------

record SourceRoleAttachmentBoundary : Set where
  constructor sourceRoleAttachmentBoundary
  field
    rolesAttachToProvenance : Bool
    rolesAttachToCanonicalTruth : Bool
    primarynessClaimRelative : Bool
    sourceRoleSeparateFromIdentity : Bool
    officialStatusCreatesIndependentTruth : Bool
    memoirStatusCreatesUnderlyingEventTruth : Bool
    investigativeRoleCreatesAllegationTruth : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open SourceRoleAttachmentBoundary public

canonicalSourceRoleAttachmentBoundary : SourceRoleAttachmentBoundary
canonicalSourceRoleAttachmentBoundary =
  sourceRoleAttachmentBoundary true false true true false false false true false

record SourceRoleAttachmentReceipt : Set where
  constructor sourceRoleAttachmentReceipt
  field
    schemaReference : String
    sourceWorldReference : String
    sourceRoleAtlasReference : String
    attachedDocumentCountReference : String
    sourceRoleIsSourceIdentity : Bool
    sourceRoleCreatesClaimTruth : Bool
    primarynessIsClaimRelative : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open SourceRoleAttachmentReceipt public

canonicalGWBSourceRoleAttachmentReceipt : SourceRoleAttachmentReceipt
canonicalGWBSourceRoleAttachmentReceipt =
  sourceRoleAttachmentReceipt
    "slr-gwb-source-role-attachment-v1"
    "sl.candidate_world_model.v0_1 after Wikimedia identity contraction"
    "fixtures/slr/gwb-claim-relative-source-roles-v1.jsonl"
    "roles_attached=10"
    false false true true false

sourceRoleAtlasAnchor : Atlas.SourceRoleBoundary
sourceRoleAtlasAnchor = Atlas.canonicalSourceRoleBoundary

identityContractionAnchor : Identity.GWBIdentityContractionBoundary
identityContractionAnchor = Identity.canonicalGWBIdentityContractionBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SourceRoleCreatesIdentity : Set where
data SourceRoleCreatesTruth : Set where
data MemoirRoleCreatesIndependentEventTruth : Set where
data OfficialRoleCreatesIndependentTruth : Set where

sourceRoleDoesNotCreateIdentity : SourceRoleCreatesIdentity → ⊥
sourceRoleDoesNotCreateIdentity ()

sourceRoleDoesNotCreateTruth : SourceRoleCreatesTruth → ⊥
sourceRoleDoesNotCreateTruth ()

memoirRoleDoesNotCreateIndependentTruth : MemoirRoleCreatesIndependentEventTruth → ⊥
memoirRoleDoesNotCreateIndependentTruth ()

officialRoleDoesNotCreateIndependentTruth : OfficialRoleCreatesIndependentTruth → ⊥
officialRoleDoesNotCreateIndependentTruth ()
