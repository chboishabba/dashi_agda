module DASHI.Biology.TarotSourceAtlas where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Bounded source atlas.
--
-- Source metadata is attached to the role actually imported.  A historical
-- source does not establish divinatory efficacy; an HCI study of interpretive
-- practice does not establish a paranormal causal channel.
------------------------------------------------------------------------

data SourceAuthority : Set where
  deckArtifact historicalMuseumSummary interpretiveHCIStudy repositoryFormalSubstrate :
    SourceAuthority

record TarotSource : Set where
  constructor tarotSource
  field
    authors : String
    title : String
    venueOrPublisher : String
    year : Nat
    identifier : String
    authority : SourceAuthority
    importedRole : String
    excludedPromotion : String

open TarotSource public

riderWaiteSmithDeckSource : TarotSource
riderWaiteSmithDeckSource =
  tarotSource
    "Pamela Colman Smith; Arthur Edward Waite"
    "Rider--Waite--Smith tarot deck"
    "William Rider and Son"
    1909
    "No DOI assigned"
    deckArtifact
    "Reference carrier, numbering, suit names, and illustrated-card tradition"
    "Does not make every later keyword canonical or establish predictive power"

metHistorySource : TarotSource
metHistorySource =
  tarotSource
    "Tim Husband"
    "Before Fortune-Telling: The History and Structure of Tarot Cards"
    "The Metropolitan Museum of Art"
    2016
    "No DOI assigned; metmuseum.org/perspectives/tarot-2"
    historicalMuseumSummary
    "Fifteenth-century game origin, four Italian suits, 56 suited cards, Fool, and 21 trumps"
    "Does not establish an ancient Egyptian origin or occult causation"

interpretiveCulturesSource : TarotSource
interpretiveCulturesSource =
  tarotSource
    "Matthew Prock; Ziv Epstein; Hope Schroeder; Amy Smith; Cassandra Lee; Vana Goblot; Farnaz Jahanbakhsh"
    "Interpretive Cultures: Resonance, randomness, and negotiated meaning for AI-assisted tarot divination"
    "arXiv, Human-Computer Interaction"
    2026
    "DOI 10.48550/arXiv.2602.11367"
    interpretiveHCIStudy
    "Subjective, plural, non-causal meaning negotiation and preservation of user agency"
    "Does not establish clinical validity, divinatory accuracy, or future causation"

typedHyperfabricSource : TarotSource
typedHyperfabricSource =
  tarotSource
    "Iulia Duta; Giulia Cassara; Fabrizio Silvestri; Pietro Lio"
    "Sheaf Hypergraph Networks"
    "arXiv"
    2023
    "DOI 10.48550/arXiv.2309.17116"
    repositoryFormalSubstrate
    "Existing DASHI typed node/hyperedge stalk and restriction-map carrier"
    "Does not import learning benchmarks, neural equivalence, or empirical performance"

canonicalTarotSources : List TarotSource
canonicalTarotSources =
  riderWaiteSmithDeckSource
  ∷ metHistorySource
  ∷ interpretiveCulturesSource
  ∷ typedHyperfabricSource
  ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ xs) = suc (listCount xs)

sourceCountIsFour : listCount canonicalTarotSources ≡ 4
sourceCountIsFour = refl
