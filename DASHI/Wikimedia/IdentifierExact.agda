module DASHI.Wikimedia.IdentifierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NATIVE WIKIMEDIA IDENTIFIERS
--
-- Source calibration:
--   * Wikidata entity/property/lexeme identifier conventions.
--   * Uploaded Aristotle RequestProject Engine.lean / PropertyEngine.lean /
--     Lexemes.lean.
--
-- These are DASHI-native carriers.  They preserve namespace/kind distinctions
-- without identifying an external identifier with DASHI concept semantics.
------------------------------------------------------------------------

record ItemId : Set where
  constructor itemId
  field rawItemId : String
open ItemId public

record PropertyId : Set where
  constructor propertyId
  field rawPropertyId : String
open PropertyId public

record LexemeId : Set where
  constructor lexemeId
  field rawLexemeId : String
open LexemeId public

record FormId : Set where
  constructor formId
  field rawFormId : String
open FormId public

record SenseId : Set where
  constructor senseId
  field rawSenseId : String
open SenseId public

data EntityId : Set where
  itemEntity : ItemId → EntityId
  propertyEntity : PropertyId → EntityId
  lexemeEntity : LexemeId → EntityId

-- Namespace separation is structural rather than a string convention.
data ItemIdIsPropertyId : Set where
data QidIsDashiConceptSemantics : Set where
data SitelinkTitleIsEntityIdentity : Set where

itemIdIsNotPropertyId : ItemIdIsPropertyId → ⊥
itemIdIsNotPropertyId ()

qidDoesNotBecomeConceptSemantics : QidIsDashiConceptSemantics → ⊥
qidDoesNotBecomeConceptSemantics ()

sitelinkTitleDoesNotBecomeEntityIdentity : SitelinkTitleIsEntityIdentity → ⊥
sitelinkTitleDoesNotBecomeEntityIdentity ()

record IdentifierBoundary : Set where
  constructor identifier-boundary
  field
    itemPropertyNamespacesDistinct : Bool
    qidEqualsConceptSemantics : Bool
    sitelinkTitleEqualsEntityIdentity : Bool

canonicalIdentifierBoundary : IdentifierBoundary
canonicalIdentifierBoundary = identifier-boundary true false false
