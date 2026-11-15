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

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Genealogical phases.
------------------------------------------------------------------------

data OriginPhase : Set where
  visualRecursiveSplit : OriginPhase
  falseBinaryStateSpace : OriginPhase
  metaPositionPowerUp : OriginPhase
  higherOrderOdds : OriginPhase
  recursiveObserver : OriginPhase
  nonlinearThresholdGeometry : OriginPhase
  probabilityDensityRhizome : OriginPhase
  padicHierarchicalRefinement : OriginPhase
  dialecticalRemainder : OriginPhase
  relationalEpistemology : OriginPhase
  ethicalProcessArchitecture : OriginPhase
  operationalStateTensor : OriginPhase
  generalizedDashiAbstraction : OriginPhase

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
    "+10% / 1.1 versus 1.0; the raw nongin metaphor explicitly compares 'my 1.1 army vs your 1 army', with 1.1 knowledge retaining one additional frame/removal level"
    "DASHI.Core.NonginOnePointOneArmyRefinementExact / number-role atlas / level-indexed recharting"
    "historical comparative-representation metaphor; not an empirical universal 10-percent law, intelligence ranking, or physical constant"

onePointOneArmyEntry : OriginSourceEntry
onePointOneArmyEntry =
  origin-source-entry
    metaPositionPowerUp
    "user-supplied raw nongin transcript"
    "1 + 1/10 = 1.1 > 1; 'my 1.1 army vs your 1 army'; one layer of removal can carry distinctions unavailable in the lower frame"
    "DASHI.Core.NonginOnePointOneArmyRefinementExact"
    "historical source for the metaphor only; the strict-projection and consumer-separation theorems are later DASHI formal reconstruction"

oddsEntry : OriginSourceEntry
oddsEntry =
  origin-source-entry
    higherOrderOdds
    "user-supplied raw origin transcript"
    "odds of odds / probability in higher orders"
    "finite branching criticality and later weighted-state models"
    "historical concept precedes later exact mathematics"

recursiveObserverEntry : OriginSourceEntry
recursiveObserverEntry =
  origin-source-entry
    recursiveObserver
    "user-supplied raw origin transcript"
    "recursive observers O(x), O(O(x)), and deeper observer-of-observer nesting"
    "DASHI.Reasoning.NonginRecursiveObserverDepthTowerExact / DASHI.Cognition.RecursiveFibreTower"
    "historical observer-nesting provenance; later depth and inverse-system theorems are DASHI reconstructions"

nonlinearThresholdEntry : OriginSourceEntry
nonlinearThresholdEntry =
  origin-source-entry
    nonlinearThresholdGeometry
    "user-supplied raw/later Nongin reconstruction stream"
    "nonlinear threshold, folding and branch-boundary visualisations used to reason about distinctions that appear or disappear under projection"
    "DASHI.Core.ThresholdResidualTrajectoryGeometryExact and domain-specific threshold-geometry owners"
    "conceptual/visual genealogy only; no universal nonlinear law or empirical threshold constant is imported"

rhizomeEntry : OriginSourceEntry
rhizomeEntry =
  origin-source-entry
    probabilityDensityRhizome
    "user-supplied 2025 perspective/probability-field material"
    "observer-relative high-dimensional shapes and overlapping/differenced density fields"
    "observer refinement / hyperfabric / social-ecology owners"
    "conceptual/visual genealogy, not a probability-measure theorem"

neutralRefineEntry : OriginSourceEntry
neutralRefineEntry =
  origin-source-entry
    padicHierarchicalRefinement
    "user-supplied later reconstruction of ternary operational rule"
    "-1 reject; 0 go deeper/refine; +1 accept"
    "DASHI.Core.EpistemicSuspensionExact"
    "historical operational semantics, not truth-value ontology"

remainderEntry : OriginSourceEntry
remainderEntry =
  origin-source-entry
    dialecticalRemainder
    "user-supplied p-adic/dialectical development stream"
    "resolution preserves an unresolved remainder that can matter downstream"
    "residual/reopenability/trajectory-residue owners"
    "later formal owners should be cited separately for exact theorems"

relationalEpistemologyEntry : OriginSourceEntry
relationalEpistemologyEntry =
  origin-source-entry
    relationalEpistemology
    "user-supplied later philosophical reconstruction, including relational/contextual learning influences"
    "knowing is situated in relation, context, perspective and reciprocal comparison rather than reduced to one master observer"
    "DASHI.Core.RelationalEpistemicProcessSourceBridgeExact and relational-perspective owners"
    "genealogical influence only; source traditions are not identified with DASHI mathematics"

ethicalProcessEntry : OriginSourceEntry
ethicalProcessEntry =
  origin-source-entry
    ethicalProcessArchitecture
    "user-supplied later philosophical/process reconstruction"
    "contextualise and relate before reflection/action; retain reciprocity, responsibility and non-collapse of source perspectives"
    "DASHI.Core.RelationalEpistemicProcessSourceBridgeExact and provenance/admissibility owners"
    "generic process abstraction only; no source author is represented as endorsing DASHI"

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
-- Phase-total atlas.
--
-- The type of genealogical phases was historically larger than the explicit
-- entry list.  `entryForPhase` closes that bookkeeping gap: every declared
-- phase now has one canonical provenance entry, without claiming mathematical
-- identity across phases.
------------------------------------------------------------------------

entryForPhase : OriginPhase → OriginSourceEntry
entryForPhase visualRecursiveSplit = screenSplitEntry
entryForPhase falseBinaryStateSpace = falseBinaryEntry
entryForPhase metaPositionPowerUp = powerUpEntry
entryForPhase higherOrderOdds = oddsEntry
entryForPhase recursiveObserver = recursiveObserverEntry
entryForPhase nonlinearThresholdGeometry = nonlinearThresholdEntry
entryForPhase probabilityDensityRhizome = rhizomeEntry
entryForPhase padicHierarchicalRefinement = neutralRefineEntry
entryForPhase dialecticalRemainder = remainderEntry
entryForPhase relationalEpistemology = relationalEpistemologyEntry
entryForPhase ethicalProcessArchitecture = ethicalProcessEntry
entryForPhase operationalStateTensor = stateTensorEntry
entryForPhase generalizedDashiAbstraction = generalizationEntry

entryForPhaseIsExact :
  (declared : OriginPhase) →
  phase (entryForPhase declared) ≡ declared
entryForPhaseIsExact visualRecursiveSplit = refl
entryForPhaseIsExact falseBinaryStateSpace = refl
entryForPhaseIsExact metaPositionPowerUp = refl
entryForPhaseIsExact higherOrderOdds = refl
entryForPhaseIsExact recursiveObserver = refl
entryForPhaseIsExact nonlinearThresholdGeometry = refl
entryForPhaseIsExact probabilityDensityRhizome = refl
entryForPhaseIsExact padicHierarchicalRefinement = refl
entryForPhaseIsExact dialecticalRemainder = refl
entryForPhaseIsExact relationalEpistemology = refl
entryForPhaseIsExact ethicalProcessArchitecture = refl
entryForPhaseIsExact operationalStateTensor = refl
entryForPhaseIsExact generalizedDashiAbstraction = refl

------------------------------------------------------------------------
-- Scope boundary.
------------------------------------------------------------------------

record DialecticOriginSourceAtlasBoundary : Set where
  constructor dialectic-origin-source-atlas-boundary
  field
    everyDeclaredOriginPhaseHasCanonicalEntry : Bool
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
    true
    false refl
    false refl
    false refl
