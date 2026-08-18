module DASHI.Ontology.WikidataBFOEntityScopeExact where

------------------------------------------------------------------------
-- WIKIDATA / BFO ENTITY ROOTS: LABEL, SCOPE, AND MAPPING STRENGTH
--
-- Working-group motivation (19 Aug 2026): Wikidata currently has two items
-- labelled "entity" in the discussion at issue:
--
--   Q35120     -- the broad Wikidata/OWL-root-facing entity item
--   Q136433660 -- the BFO Entity-facing item (BFO_0000001)
--
-- The point of this module is not to settle the metaphysics of existence.
-- It formalises the weaker and operationally safer claim needed by the
-- alignment checker: identical labels do not determine ontology scope, and
-- the three currently-used BFO linkage mechanisms have different strengths.
--
-- Current Wikidata/BFO project surfaces consulted for this contract:
--   * Wikidata:WikiProject Ontology/Mapping Wikidata To BFO
--   * Property talk:P12602 (BFO class ID)
--   * Q35120 / Q136433660 and Talk:Q136433660
--
-- In particular, the BFO project query keeps P2888, P1709, and P12602 as
-- distinct columns.  This module deliberately does the same.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Two roots can share a public label while carrying different scope.
------------------------------------------------------------------------

data EntityRoot : Set where
  wikidataEntityQ35120 : EntityRoot
  bfoEntityQ136433660 : EntityRoot

rootLabel : EntityRoot → String
rootLabel wikidataEntityQ35120 = "entity"
rootLabel bfoEntityQ136433660 = "entity"

data RootScope : Set where
  wikidataUniverseScope : RootScope
  bfoUpperOntologyScope : RootScope

rootScope : EntityRoot → RootScope
rootScope wikidataEntityQ35120 = wikidataUniverseScope
rootScope bfoEntityQ136433660 = bfoUpperOntologyScope

entityLabelsCoincide :
  rootLabel wikidataEntityQ35120 ≡ rootLabel bfoEntityQ136433660
entityLabelsCoincide = refl

rootScopesDiffer : wikidataUniverseScope ≡ bfoUpperOntologyScope → ⊥
rootScopesDiffer ()

record LabelOnlyScopeDecoder : Set where
  constructor labelOnlyScopeDecoder
  field
    decodeScope : String → RootScope
    q35120Decoded :
      decodeScope (rootLabel wikidataEntityQ35120) ≡ wikidataUniverseScope
    q136433660Decoded :
      decodeScope (rootLabel bfoEntityQ136433660) ≡ bfoUpperOntologyScope

open LabelOnlyScopeDecoder public

sameEntityLabelCannotDetermineBothScopes :
  LabelOnlyScopeDecoder → ⊥
sameEntityLabelCannotDetermineBothScopes decoder =
  rootScopesDiffer
    (trans
      (sym (q35120Decoded decoder))
      (trans
        (cong (decodeScope decoder) entityLabelsCoincide)
        (q136433660Decoded decoder)))

------------------------------------------------------------------------
-- Mapping-property strength is typed, not a single "mapped to BFO" bit.
------------------------------------------------------------------------

data BFOLinkKind : Set where
  p12602BFOClassIdentifier : BFOLinkKind
  p2888ExactMatch : BFOLinkKind
  p1709EquivalentClass : BFOLinkKind
  p279Subclass : BFOLinkKind

data InferenceLanguage : Set where
  identifierLookup : InferenceLanguage
  semanticInterchange : InferenceLanguage
  classEquivalence : InferenceLanguage
  subclassReasoning : InferenceLanguage
  disjointnessTransport : InferenceLanguage

supportsLanguage : BFOLinkKind → InferenceLanguage → Bool
supportsLanguage p12602BFOClassIdentifier identifierLookup = true
supportsLanguage p12602BFOClassIdentifier semanticInterchange = false
supportsLanguage p12602BFOClassIdentifier classEquivalence = false
supportsLanguage p12602BFOClassIdentifier subclassReasoning = false
supportsLanguage p12602BFOClassIdentifier disjointnessTransport = false
supportsLanguage p2888ExactMatch identifierLookup = false
supportsLanguage p2888ExactMatch semanticInterchange = true
supportsLanguage p2888ExactMatch classEquivalence = false
supportsLanguage p2888ExactMatch subclassReasoning = false
supportsLanguage p2888ExactMatch disjointnessTransport = false
supportsLanguage p1709EquivalentClass identifierLookup = false
supportsLanguage p1709EquivalentClass semanticInterchange = false
supportsLanguage p1709EquivalentClass classEquivalence = true
supportsLanguage p1709EquivalentClass subclassReasoning = false
supportsLanguage p1709EquivalentClass disjointnessTransport = false
supportsLanguage p279Subclass identifierLookup = false
supportsLanguage p279Subclass semanticInterchange = false
supportsLanguage p279Subclass classEquivalence = false
supportsLanguage p279Subclass subclassReasoning = true
supportsLanguage p279Subclass disjointnessTransport = false

p12602LicensesIdentifierLookup :
  supportsLanguage p12602BFOClassIdentifier identifierLookup ≡ true
p12602LicensesIdentifierLookup = refl

p12602DoesNotLicenseSemanticInterchange :
  supportsLanguage p12602BFOClassIdentifier semanticInterchange ≡ false
p12602DoesNotLicenseSemanticInterchange = refl

p2888DoesNotBecomeEquivalentClassByType :
  supportsLanguage p2888ExactMatch classEquivalence ≡ false
p2888DoesNotBecomeEquivalentClassByType = refl

p1709CarriesClassEquivalenceRole :
  supportsLanguage p1709EquivalentClass classEquivalence ≡ true
p1709CarriesClassEquivalenceRole = refl

subclassDoesNotBecomeExactMatch :
  supportsLanguage p279Subclass semanticInterchange ≡ false
subclassDoesNotBecomeExactMatch = refl

noSingleListedLinkLicensesDisjointnessTransport :
  (kind : BFOLinkKind) →
  supportsLanguage kind disjointnessTransport ≡ false
noSingleListedLinkLicensesDisjointnessTransport p12602BFOClassIdentifier = refl
noSingleListedLinkLicensesDisjointnessTransport p2888ExactMatch = refl
noSingleListedLinkLicensesDisjointnessTransport p1709EquivalentClass = refl
noSingleListedLinkLicensesDisjointnessTransport p279Subclass = refl

------------------------------------------------------------------------
-- Snapshot packet: data assertion remains separate from inference licence.
------------------------------------------------------------------------

record EntityRootSnapshot : Set where
  constructor entityRootSnapshot
  field
    q35120Label : String
    q136433660Label : String
    q136433660BFOIdentifier : String
    q136433660SubclassOfQ35120 : Bool
    sourceNote : String

open EntityRootSnapshot public

canonicalEntityRootSnapshot : EntityRootSnapshot
canonicalEntityRootSnapshot =
  entityRootSnapshot
    "entity"
    "entity"
    "0000001"
    true
    "Wikidata BFO mapping/project and Talk:Q136433660 snapshot, 2026-08-19"

record BFOEntityScopeBoundary : Set where
  constructor bfoEntityScopeBoundary
  field
    sameEnglishLabelMeansSameExtension : Bool
    externalIdentifierMeansExactSemanticMatch : Bool
    exactMatchMeansEquivalentClassByPropertyType : Bool
    subclassMeansEquivalence : Bool
    oneLinkAloneLicensesDisjointnessTransport : Bool
    mappingStrengthMustRemainTyped : Bool

canonicalBFOEntityScopeBoundary : BFOEntityScopeBoundary
canonicalBFOEntityScopeBoundary =
  bfoEntityScopeBoundary false false false false false true
