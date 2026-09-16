module DASHI.Interop.SLRMultilingualPNFRoleCompatibilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRMultilingualWikimediaParserCompatibilityExact as Multi

------------------------------------------------------------------------
-- MULTILINGUAL PNF ROLE-CARRIER COMPATIBILITY
--
-- Runtime:
--   tools/slr-discourse-reconstruct/slr_multilingual_pnf_role_compat.py
--   tools/slr-discourse-reconstruct/run_multilingual_pnf_role_compat.sh
--
-- Each same-QID language surface is reduced to a coarse dependency-role
-- signature: subject / object / predicate-root / negation / auxiliary /
-- clause / coordination.  Pairwise overlap can demonstrate that the same
-- structural carrier vocabulary is representable across language parsers.
-- It does not establish translation equivalence, sentence alignment, or
-- claim-semantic equivalence.
------------------------------------------------------------------------

record MultilingualPNFRoleBoundary : Set where
  constructor multilingualPNFRoleBoundary
  field
    sharedQidPaysEntityIdentity : Bool
    trainedDependencyParsersRequired : Bool
    roleFamiliesComparedAcrossLanguages : Bool
    roleOverlapPaysTranslationEquivalence : Bool
    roleOverlapPaysSentenceAlignment : Bool
    roleOverlapPaysClaimSemanticEquivalence : Bool
    originalLanguageSurfaceRetained : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open MultilingualPNFRoleBoundary public

canonicalMultilingualPNFRoleBoundary : MultilingualPNFRoleBoundary
canonicalMultilingualPNFRoleBoundary =
  multilingualPNFRoleBoundary true true true false false false true true false

record MultilingualPNFRoleReceipt : Set where
  constructor multilingualPNFRoleReceipt
  field
    schemaReference : String
    sourceMultilingualReference : String
    qidCountReference : String
    surfaceCountReference : String
    pairCountReference : String
    subjectPredicateObjectCarrierReference : String
    translationEquivalencePaid : Bool
    sentenceAlignmentPaid : Bool
    claimSemanticEquivalencePaid : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open MultilingualPNFRoleReceipt public

canonicalMultilingualPNFRoleReceipt : MultilingualPNFRoleReceipt
canonicalMultilingualPNFRoleReceipt =
  multilingualPNFRoleReceipt
    "slr-multilingual-pnf-role-compat-v1"
    "slr-multilingual-wikimedia-parser-compat-v1"
    "runtime receipt:qids"
    "runtime receipt:surfaces"
    "runtime receipt:language_pairs"
    "runtime receipt:surfaces_with_subject_predicate_object + pairs_with_core_role_carrier_compatibility"
    false false false true false

multilingualParserAnchor : Multi.MultilingualIdentityBoundary
multilingualParserAnchor = Multi.canonicalMultilingualIdentityBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RoleOverlapIsTranslationEquivalence : Set where
data RoleOverlapIsSentenceAlignment : Set where
data RoleOverlapIsClaimSemanticEquivalence : Set where
data SharedQidErasesLanguageSurfaceProvenance : Set where

roleOverlapDoesNotCreateTranslationEquivalence : RoleOverlapIsTranslationEquivalence → ⊥
roleOverlapDoesNotCreateTranslationEquivalence ()

roleOverlapDoesNotCreateSentenceAlignment : RoleOverlapIsSentenceAlignment → ⊥
roleOverlapDoesNotCreateSentenceAlignment ()

roleOverlapDoesNotCreateClaimSemanticEquivalence : RoleOverlapIsClaimSemanticEquivalence → ⊥
roleOverlapDoesNotCreateClaimSemanticEquivalence ()

sharedQidDoesNotEraseLanguageSurfaceProvenance : SharedQidErasesLanguageSurfaceProvenance → ⊥
sharedQidDoesNotEraseLanguageSurfaceProvenance ()
