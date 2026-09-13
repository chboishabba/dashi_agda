module DASHI.Wikimedia.WikipediaFirstLinkNetworkExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- WIKIPEDIA FIRST-LINK NETWORK
--
-- Source 1:
-- Mark Ibrahim, Christopher M. Danforth, Peter Sheridan Dodds,
-- "Connecting every bit of knowledge: The structure of Wikipedia's First
-- Link Network", Journal of Computational Science 19 (2017), 21-30.
-- DOI: 10.1016/j.jocs.2016.12.001
--
-- Source 2:
-- Maxime Gabella, "Cultural Structures of Knowledge from Wikipedia Networks
-- of First Links", IEEE Transactions on Network Science and Engineering
-- 6(3) (2019), 249-252.
-- DOI: 10.1109/TNSE.2018.2812788
--
-- The point of this owner is the boundary, not a replay of either dataset:
-- first-link reachability is indexed by language edition, revision/snapshot,
-- and link-selection/parser policy.  Therefore the folklore sentence
-- "everything leads to Philosophy" is never promoted to an invariant of
-- Wikipedia as a whole.
------------------------------------------------------------------------

record FirstLinkSnapshot : Set where
  constructor first-link-snapshot
  field
    languageEdition : String
    revisionOrDumpIdentity : String
    linkSelectionPolicy : String
    parserPolicy : String
open FirstLinkSnapshot public

record FirstLinkStudySource : Set where
  constructor first-link-study-source
  field
    authors : String
    title : String
    publication : String
    doi : String
open FirstLinkStudySource public

ibrahimDanforthDodds2017 : FirstLinkStudySource
ibrahimDanforthDodds2017 =
  first-link-study-source
    "Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds"
    "Connecting every bit of knowledge: The structure of Wikipedia's First Link Network"
    "Journal of Computational Science 19 (2017), 21-30"
    "10.1016/j.jocs.2016.12.001"

gabella2019 : FirstLinkStudySource
gabella2019 =
  first-link-study-source
    "Maxime Gabella"
    "Cultural Structures of Knowledge from Wikipedia Networks of First Links"
    "IEEE Transactions on Network Science and Engineering 6(3) (2019), 249-252"
    "10.1109/TNSE.2018.2812788"

record FirstLinkGraphObservation : Set where
  constructor first-link-graph-observation
  field
    snapshot : FirstLinkSnapshot
    source : FirstLinkStudySource
    articleCount : Nat
    philosophyHasLargestTraversalFunnel : Bool
    philosophyDominanceStatement : String
    languageDependenceObserved : Bool
    revisionDependenceRetained : Bool
open FirstLinkGraphObservation public

-- The Ibrahim et al. study used approximately 4.7 million English articles.
-- We retain their qualitative result exactly at the source boundary: Philosophy
-- directed more paths than any other article by two orders of magnitude.
ibrahimEnglishObservation : FirstLinkGraphObservation
ibrahimEnglishObservation =
  first-link-graph-observation
    (first-link-snapshot
      "English Wikipedia"
      "study snapshot used by Ibrahim-Danforth-Dodds; not asserted current"
      "first qualifying article link"
      "study-specific Wikipedia parsing/exclusion policy")
    ibrahimDanforthDodds2017
    4700000
    true
    "Philosophy directed more first-link paths than any other article by two orders of magnitude"
    false
    true

-- Gabella's multilingual work is retained as evidence that the central/core
-- concepts vary across language editions; European and East-Asian editions do
-- not share one universal first-link attractor.
gabellaMultilingualObservation : FirstLinkGraphObservation
gabellaMultilingualObservation =
  first-link-graph-observation
    (first-link-snapshot
      "multiple Wikipedia language editions"
      "study snapshots used by Gabella; not asserted current"
      "first qualifying article link"
      "study-specific multilingual parsing policy")
    gabella2019
    0
    false
    "European editions tend toward Philosophy/Science-like cores while East-Asian editions may center Human/Earth-like concepts"
    true
    true

------------------------------------------------------------------------
-- Formal graph boundary.
------------------------------------------------------------------------

record RevisionIndexedFirstLinkGraph (Node : Set) : Set₁ where
  field
    snapshot : FirstLinkSnapshot
    firstLink : Node → Node
open RevisionIndexedFirstLinkGraph public

record ReachabilityObservation {Node : Set}
  (G : RevisionIndexedFirstLinkGraph Node) : Set₁ where
  field
    start : Node
    target : Node
    hops : Nat
    observedAtSnapshot : Bool
open ReachabilityObservation public

-- Forbidden promotions.
data FirstLinkUniversalInvariant : Set where
data PhilosophyIsTimelessWikipediaSink : Set where
data CrossLanguageFirstLinkIdentity : Set where
data FirstLinkReachabilityIsSemanticTruth : Set where

firstLinkObservationDoesNotCreateUniversalInvariant :
  FirstLinkUniversalInvariant → ⊥
firstLinkObservationDoesNotCreateUniversalInvariant ()

philosophyIsNotTypedAsTimelessSink :
  PhilosophyIsTimelessWikipediaSink → ⊥
philosophyIsNotTypedAsTimelessSink ()

languageEditionsDoNotCollapse :
  CrossLanguageFirstLinkIdentity → ⊥
languageEditionsDoNotCollapse ()

firstLinkReachabilityDoesNotCreateSemanticTruth :
  FirstLinkReachabilityIsSemanticTruth → ⊥
firstLinkReachabilityDoesNotCreateSemanticTruth ()

record FirstLinkNetworkBoundary : Set where
  constructor first-link-network-boundary
  field
    languageIndexed : Bool
    revisionIndexed : Bool
    parserPolicyIndexed : Bool
    sourceAttributed : Bool
    universalPhilosophyClaim : Bool
    semanticTruthPromotion : Bool

canonicalFirstLinkNetworkBoundary : FirstLinkNetworkBoundary
canonicalFirstLinkNetworkBoundary =
  first-link-network-boundary true true true true false false
