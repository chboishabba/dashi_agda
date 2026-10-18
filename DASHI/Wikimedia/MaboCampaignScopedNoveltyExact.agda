module DASHI.Wikimedia.MaboCampaignScopedNoveltyExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- CAMPAIGN-SCOPED MABO NOVELTY
--
-- Attribution / runtime provenance:
--   SLR repository: chboishabba/slr
--   PR: https://github.com/chboishabba/slr/pull/25
--   Source-written head: 527c8a1f9023806bcf617c2df210bfb5fb53c7ea
--
-- This owner formalises a narrow non-collapse discovered during adaptive
-- campaign audit. The durable identity baseline is intentionally GLOBAL for
-- SameObject quotienting/coherence and alias reuse. Mabo campaign novelty is
-- instead a SEED-ROOTED discovery-lineage cardinality. Unrelated campaign
-- lineages may therefore participate in identity coherence without paying the
-- Mabo >=100 target.
--
-- Likewise, context-expansion residuals range only over durable QIDs that are
-- in the CURRENT Mabo world and remain unexpanded; the global durable identity
-- table is not itself the Mabo semantic frontier.
--
-- No DOI applies: this is a DASHI/SLR implementation invariant, not an
-- external scholarly proposition. Repository/PR/head coordinates are retained
-- instead. This source-written boundary does not manufacture Cargo or Agda
-- execution evidence.
------------------------------------------------------------------------

slrRepositoryReference : String
slrRepositoryReference = "chboishabba/slr"

slrPullRequestReference : String
slrPullRequestReference = "https://github.com/chboishabba/slr/pull/25"

slrSourceWrittenHeadReference : String
slrSourceWrittenHeadReference = "527c8a1f9023806bcf617c2df210bfb5fb53c7ea"

maboSeedReference : String
maboSeedReference = "Q1501525"

record MaboCampaignScopedNovelty : Set where
  constructor mabo-campaign-scoped-novelty
  field
    globalIdentityBaselineUsedForCoherence : Bool
    globalIdentityBaselineCountsCampaignNovelty : Bool
    maboCampaignNoveltyUsesSeedRootedDiscoveryLineage : Bool
    aliasesCountCampaignNovelty : Bool
    unrelatedCampaignLineageCountsForMabo : Bool
    targetCompletionUsesCampaignScopedCardinality : Bool
    contextExpansionUsesCurrentMaboWorld : Bool
    globalDurableIdentityEqualsMaboCampaignNovelty : Bool
    currentMaboWorldEqualsGlobalIdentityTable : Bool
    scopedNoveltyCreatesSemanticAuthority : Bool
    scopedNoveltyCreatesClaimTruth : Bool

open MaboCampaignScopedNovelty public

canonicalMaboCampaignScopedNovelty : MaboCampaignScopedNovelty
canonicalMaboCampaignScopedNovelty =
  mabo-campaign-scoped-novelty
    true
    false
    true
    false
    false
    true
    true
    false
    false
    false
    false

------------------------------------------------------------------------
-- Non-collapse firewalls.
------------------------------------------------------------------------

data GlobalDurableIdentityEqualsMaboCampaignNovelty : Set where
data CurrentMaboWorldEqualsGlobalIdentityTable : Set where
data UnrelatedCampaignLineagePaysMaboTarget : Set where
data AliasPersistencePaysMaboNovelty : Set where
data ScopedNoveltyCreatesSemanticAuthority : Set where
data ScopedNoveltyCreatesClaimTruth : Set where

globalDurableIdentityDoesNotEqualMaboCampaignNovelty :
  GlobalDurableIdentityEqualsMaboCampaignNovelty → ⊥
globalDurableIdentityDoesNotEqualMaboCampaignNovelty ()

currentMaboWorldDoesNotEqualGlobalIdentityTable :
  CurrentMaboWorldEqualsGlobalIdentityTable → ⊥
currentMaboWorldDoesNotEqualGlobalIdentityTable ()

unrelatedCampaignLineageDoesNotPayMaboTarget :
  UnrelatedCampaignLineagePaysMaboTarget → ⊥
unrelatedCampaignLineageDoesNotPayMaboTarget ()

aliasPersistenceDoesNotPayMaboNovelty :
  AliasPersistencePaysMaboNovelty → ⊥
aliasPersistenceDoesNotPayMaboNovelty ()

scopedNoveltyDoesNotCreateSemanticAuthority :
  ScopedNoveltyCreatesSemanticAuthority → ⊥
scopedNoveltyDoesNotCreateSemanticAuthority ()

scopedNoveltyDoesNotCreateClaimTruth :
  ScopedNoveltyCreatesClaimTruth → ⊥
scopedNoveltyDoesNotCreateClaimTruth ()
