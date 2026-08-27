module DASHI.Core.DialecticOriginSourceAtlasExact where

------------------------------------------------------------------------
-- DIALECTIC ORIGIN SOURCE ATLAS
--
-- This is provenance infrastructure, not empirical authority.
--
-- Source basis:
--   User-supplied DASHI origin/reconstruction material recovered in the current
--   project conversation.  The material distinguishes a bottom-up origin stream
--   (screen splitting, debate state-space, +10%, odds of odds, recursive
--   observers, probability-wave visualisations, p-adic exploration, remainder)
--   from later philosophical/relational synthesis and from the subsequent
--   executable state-tensor/motif operationalisation.
--
-- The purpose of this module is to stop future code/comments from presenting
-- later formal owners as if they were the historical source of the ideas.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Genealogical phases.
------------------------------------------------------------------------

data OriginPhase : Set where
  visualRecursiveSplit
  falseBinaryStateSpace
  metaPositionPowerUp
  higherOrderOdds
  recursiveObserver
  nonlinearThresholdGeometry
  probabilityDensityRhizome
  padicHierarchicalRefinement
  dialecticalRemainder
  relationalEpistemology
  ethicalProcessArchitecture
  operationalStateTensor
  generalizedDashiAbstraction
  : OriginPhase

record OriginSourceEntry : Set where
  constructor origin-source-entry
  field
    phase : OriginPhase
    sourceClass : String
    historicalSummary : String
    laterFormalOwner : String
    authorityNote : String

open OriginSourceEntry public

screenSplitEntry : OriginSourceEntry
screenSplitEntry =
  origin-source-entry
    visualRecursiveSplit
    "user-supplied raw origin / nongin-like transcript"
    "recursive screen/window halving: 1, 1/2, 1/4, 1/8, ..."
    "later recursive-fibre / refinement owners"
    "historical provenance only"

falseBinaryEntry : OriginSourceEntry
falseBinaryEntry =
  origin-source-entry
    falseBinaryStateSpace
    "user-supplied raw origin transcript"
    "two-person debate presented as binary but internally branches into a larger state-space"
    "observer/fibre/non-factorability owners"
    "retrospective formal correspondence, not historical derivation proof"

powerUpEntry : OriginSourceEntry
powerUpEntry =
  origin-source-entry
    metaPositionPowerUp
    "user-supplied raw origin transcript"
    "+10% / 1.1 versus 1.0 shorthand for one additional meta-level of representation"
    "number-role atlas / level-indexed recharting"
    "not an empirical universal 10-percent law"

oddsEntry : OriginSourceEntry
oddsEntry =
  origin-source-entry
    higherOrderOdds
    "user-supplied raw origin transcript"
    "odds of odds / probability in higher orders"
    "finite branching criticality and later weighted-state models"
    "historical concept precedes later exact mathematics"

neutralRefineEntry : OriginSourceEntry
neutralRefineEntry =
  origin-source-entry
    padicHierarchicalRefinement
    "user-supplied later reconstruction of ternary operational rule"
    "-1 reject; 0 go deeper/refine; +1 accept"
    "DASHI.Core.EpistemicSuspensionExact"
    "historical operational semantics, not truth-value ontology"

rhizomeEntry : OriginSourceEntry
rhizomeEntry =
  origin-source-entry
    probabilityDensityRhizome
    "user-supplied 2025 perspective/probability-field material"
    "observer-relative high-dimensional shapes and overlapping/differenced density fields"
    "observer refinement / hyperfabric / social-ecology owners"
    "conceptual/visual genealogy, not a probability-measure theorem"

remainderEntry : OriginSourceEntry
remainderEntry =
  origin-source-entry
    dialecticalRemainder
    "user-supplied p-adic/dialectical development stream"
    "resolution preserves an unresolved remainder that can matter downstream"
    "residual/reopenability/trajectory-residue owners"
    "later formal owners should be cited separately for exact theorems"

stateTensorEntry : OriginSourceEntry
stateTensorEntry =
  origin-source-entry
    operationalStateTensor
    "later DASHI state-tensor / TRADER_CANTEXT operationalisation"
    "3x3 ternary state compressed to M1...M9/M10 supervisory motifs"
    "DASHI.Reasoning.DialecticMotifKernel"
    "operational descendant, not identical to the historical 0-11 spectrum"

generalizationEntry : OriginSourceEntry
generalizationEntry =
  origin-source-entry
    generalizedDashiAbstraction
    "modern DASHI formal corpus"
    "observers, quotients, residuals, traces, admissibility, refusal, recharting"
    "DASHI.Core and domain-specific exact owners"
    "formal descendant with independent source attribution per theorem"

------------------------------------------------------------------------
-- Scope boundary.
------------------------------------------------------------------------

record DialecticOriginSourceAtlasBoundary : Set where
  constructor dialectic-origin-source-atlas-boundary
  field
    historicalSourceIsExternalScientificAuthority : Bool
    historicalSourceIsExternalScientificAuthorityIsFalse :
      historicalSourceIsExternalScientificAuthority ≡ false
    laterFormalOwnerIsClaimedAsOriginalHistoricalSource : Bool
    laterFormalOwnerIsClaimedAsOriginalHistoricalSourceIsFalse :
      laterFormalOwnerIsClaimedAsOriginalHistoricalSource ≡ false
    genealogyImpliesMathematicalIdentityAcrossPhases : Bool
    genealogyImpliesMathematicalIdentityAcrossPhasesIsFalse :
      genealogyImpliesMathematicalIdentityAcrossPhases ≡ false

canonicalDialecticOriginSourceAtlasBoundary : DialecticOriginSourceAtlasBoundary
canonicalDialecticOriginSourceAtlasBoundary =
  dialectic-origin-source-atlas-boundary
    false refl
    false refl
    false refl
