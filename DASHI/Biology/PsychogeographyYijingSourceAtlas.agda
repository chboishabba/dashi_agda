module DASHI.Biology.PsychogeographyYijingSourceAtlas where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Bibliographic provenance.  A source record constrains imported role and
-- excluded promotion; citation does not import a theorem automatically.
------------------------------------------------------------------------

data IdentifierKind : Set where
  doiIdentifier : IdentifierKind
  isbnIdentifier : IdentifierKind
  noDOIAssigned : IdentifierKind
  gameWorkIdentifier : IdentifierKind
  webPublicationIdentifier : IdentifierKind

record SourceRecord : Set where
  constructor sourceRecord
  field
    authors : String
    title : String
    venueOrPublisher : String
    year : Nat
    identifierKind : IdentifierKind
    identifier : String
    importedRole : String
    excludedPromotion : String

open SourceRecord public

debordDeriveSource : SourceRecord
debordDeriveSource =
  sourceRecord "Guy Debord" "Theory of the Derive"
    "Les Levres Nues 9" 1956 noDOIAssigned "NO_DOI_ASSIGNED"
    "derive, attractions, repulsions, interruption of habitual routing"
    "not a quantitative law of pedestrian dynamics"

debordWolmanDetournementSource : SourceRecord
debordWolmanDetournementSource =
  sourceRecord "Guy Debord; Gil J. Wolman" "A User's Guide to Detournement"
    "Les Levres Nues 8" 1956 noDOIAssigned "NO_DOI_ASSIGNED"
    "retained carrier with altered context and relation"
    "not proof that every reuse is emancipatory"

lefebvreProductionSpaceSource : SourceRecord
lefebvreProductionSpaceSource =
  sourceRecord "Henri Lefebvre" "The Production of Space"
    "Anthropos; Blackwell English translation" 1974 isbnIdentifier
    "ISBN 978-0-631-18177-4"
    "space as socially produced and lived rather than neutral container"
    "not a formal equivalence between social space and one hypergraph"

noraMemoryHistorySource : SourceRecord
noraMemoryHistorySource =
  sourceRecord "Pierre Nora" "Between Memory and History: Les Lieux de Memoire"
    "Representations 26" 1989 doiIdentifier "10.2307/2928520"
    "collective memory and historically saturated sites"
    "not a theorem that every place stores one recoverable history"

brewinDualRepresentationSource : SourceRecord
brewinDualRepresentationSource =
  sourceRecord "Chris R. Brewin; Tim Dalgleish; Stephen Joseph"
    "A Dual Representation Theory of Posttraumatic Stress Disorder"
    "Psychological Review 103(4)" 1996 doiIdentifier
    "10.1037/0033-295X.103.4.670"
    "separation of memory content, cue access and source/context relation"
    "not diagnosis, prevalence, treatment advice or validation of this finite model"

chengYijingYangSource : SourceRecord
chengYijingYangSource =
  sourceRecord "Dennis Chi-Hsiung Cheng"
    "Interpretations of Yang in the Yijing Commentarial Traditions"
    "Journal of Chinese Philosophy 35(2)" 2008 doiIdentifier
    "10.1111/j.1540-6253.2008.00475.x"
    "historically bounded Yijing polarity and commentarial interpretation"
    "not authority for the DASHI ternary extension"

luWeiYijingSource : SourceRecord
luWeiYijingSource =
  sourceRecord "Xunjian Lu; Fuming Wei"
    "Simply Do Not Divine: On the Cosmology, Moral Constraints, and Self-Transcendence of Divination in the Yijing"
    "Religions 17(7)" 2026 doiIdentifier "10.3390/rel17070796"
    "recent account of divination as constrained practice rather than prediction alone"
    "not proof of external predictive accuracy"

dutaHypergraphSource : SourceRecord
dutaHypergraphSource =
  sourceRecord "Iulia Duta; Giulia Cassara; Fabrizio Silvestri; Pietro Lio"
    "Sheaf Hypergraph Networks" "arXiv" 2023 doiIdentifier
    "10.48550/arXiv.2309.17116"
    "typed node/edge stalk and restriction-map architecture already used in-repo"
    "not imported benchmark performance or learned urban model"

zaumDiscoSource : SourceRecord
zaumDiscoSource =
  sourceRecord "ZA/UM" "Disco Elysium"
    "ZA/UM; video game" 2019 gameWorkIdentifier "NO_DOI_ASSIGNED"
    "fictional polyphony, urban address, ruins, Pale and clue-constrained exploration"
    "not empirical neuroscience, geography or physics"

zaumThoughtCabinetSource : SourceRecord
zaumThoughtCabinetSource =
  sourceRecord "ZA/UM" "Introducing the Thought Cabinet"
    "Official development blog" 2019 webPublicationIdentifier "NO_DOI_ASSIGNED"
    "finite thought capacity and place-acquired map-transforming frames"
    "not a cognitive-capacity measurement theorem"

allPsychogeographySources : List SourceRecord
allPsychogeographySources =
  debordDeriveSource
  ∷ debordWolmanDetournementSource
  ∷ lefebvreProductionSpaceSource
  ∷ noraMemoryHistorySource
  ∷ brewinDualRepresentationSource
  ∷ chengYijingYangSource
  ∷ luWeiYijingSource
  ∷ dutaHypergraphSource
  ∷ zaumDiscoSource
  ∷ zaumThoughtCabinetSource
  ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ xs) = suc (listCount xs)

sourceAtlasHasTenRecords : listCount allPsychogeographySources ≡ 10
sourceAtlasHasTenRecords = refl
