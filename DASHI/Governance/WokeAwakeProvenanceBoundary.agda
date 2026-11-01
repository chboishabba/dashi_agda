module DASHI.Governance.WokeAwakeProvenanceBoundary where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.EpistemicAttractorCore as Attractor

------------------------------------------------------------------------
-- Woke / awake provenance boundary.
--
-- The formal similarity "the surface story is inadequate" does not erase
-- historical provenance.  In particular, the Black-American survival-
-- vigilance history of "stay woke" is kept distinct from later generic,
-- pejorative, conspiratorial or counter-cultural uses of wake/awake language.
--
-- Archival precedent:
--   Huddie Ledbetter (Lead Belly), "Scottsboro Boys", recorded for the
--   John A. Lomax / Alan Lomax field collection, 1938.
--   Library of Congress, American Folklife Center; no DOI assigned.
--
-- The archival item is a provenance anchor, not a theorem that every later use
-- of "woke" has one invariant meaning or political programme.
------------------------------------------------------------------------

record VocabularySource : Set where
  constructor vocabularySource
  field
    speakerOrAuthor : String
    title : String
    archiveOrVenue : String
    date : String
    identifier : String
    provenanceRole : String
    sourceCreatesFixedModernMeaning : Bool

open VocabularySource public

leadBellyScottsboroSource : VocabularySource
leadBellyScottsboroSource =
  vocabularySource
    "Huddie Ledbetter (Lead Belly); recorded by John A. Lomax / Alan Lomax"
    "Scottsboro Boys"
    "Library of Congress, American Folklife Center"
    "1938"
    "John A. Lomax / Alan Lomax field collection; archival recording; no DOI assigned"
    "Black-American survival-vigilance provenance anchor; does not by itself settle all later lexical history"
    false

data VocabularyLane : Set where
  blackSurvivalVigilanceLane : VocabularyLane
  structuralCriticalConsciousnessLane : VocabularyLane
  genericProgressiveLane : VocabularyLane
  pejorativeCultureWarLane : VocabularyLane
  conspiratorialAwakeLane : VocabularyLane

record ProvenanceBinding : Set where
  constructor provenanceBinding
  field
    lane : VocabularyLane
    source : VocabularySource
    historicalProvenancePreserved : Bool
    lexicalSimilarityCreatesPoliticalIdentity : Bool
    laterSemanticCaptureErasesEarlierProvenance : Bool

canonicalBlackWokeProvenance : ProvenanceBinding
canonicalBlackWokeProvenance =
  provenanceBinding
    blackSurvivalVigilanceLane
    leadBellyScottsboroSource
    true
    false
    false

------------------------------------------------------------------------
-- Causal-resolution discriminator.
------------------------------------------------------------------------

record WokeAwakeEpistemicBoundary : Set where
  constructor wokeAwakeEpistemicBoundary
  field
    sharedSeeingMetaphorMakesLanesEquivalent : Bool
    blackStructuralVigilanceEqualsConspiratorialClosure : Bool
    pejorativeReuseErasesBlackProvenance : Bool
    criticalConsciousnessMustPermitInspectingNamedEdges : Bool
    conspiratorialClosureCanBeDiagnosedFromVocabularyAlone : Bool

canonicalWokeAwakeEpistemicBoundary : WokeAwakeEpistemicBoundary
canonicalWokeAwakeEpistemicBoundary =
  wokeAwakeEpistemicBoundary false false false true false

record WokeAwakeProvenanceReceipt : Set where
  constructor wokeAwakeProvenanceReceipt
  field
    label : String
    blackWokeProvenance : ProvenanceBinding
    epistemicAttractorReceipt : Attractor.EpistemicAttractorReceipt
    boundary : WokeAwakeEpistemicBoundary

canonicalWokeAwakeProvenanceReceipt : WokeAwakeProvenanceReceipt
canonicalWokeAwakeProvenanceReceipt =
  wokeAwakeProvenanceReceipt
    "woke/awake provenance and causal-resolution separation"
    canonicalBlackWokeProvenance
    Attractor.canonicalEpistemicAttractorReceipt
    canonicalWokeAwakeEpistemicBoundary
