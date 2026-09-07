module DASHI.Wikimedia.NativeStatementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

import DASHI.Wikimedia.IdentifierExact as Id

------------------------------------------------------------------------
-- NATIVE WIKIDATA STATEMENT CARRIER
--
-- Source calibration:
--   uploaded Aristotle RequestProject Snaks.lean, Ranks.lean,
--   Qualifiers.lean, Provenance.lean, Sitelinks.lean, Lexemes.lean.
--
-- Unlike the older epistemic adapter, this layer first preserves Wikidata's
-- object language.  Epistemic interpretation is a downstream projection.
------------------------------------------------------------------------

data NativeValue : Set where
  entityValue : Id.EntityId → NativeValue
  stringValue : String → NativeValue
  externalIdValue : String → NativeValue
  timeValue : String → NativeValue
  quantityValue : String → NativeValue
  monolingualTextValue : String → String → NativeValue

data Snak : Set where
  valueSnak : NativeValue → Snak
  someValue : Snak
  noValue : Snak

data StatementRank : Set where
  preferred normal deprecated : StatementRank

record Qualifier : Set where
  constructor qualifier
  field
    qualifierProperty : Id.PropertyId
    qualifierSnak : Snak
open Qualifier public

record ReferenceSnak : Set where
  constructor referenceSnak
  field
    referenceProperty : Id.PropertyId
    referenceSnakValue : Snak
open ReferenceSnak public

record ReferenceBlock : Set where
  constructor referenceBlock
  field
    referenceSnaks : List ReferenceSnak
    referenceId : String
open ReferenceBlock public

record Statement : Set where
  constructor statement
  field
    statementId : String
    statementSubject : Id.EntityId
    statementProperty : Id.PropertyId
    mainsnak : Snak
    statementRank : StatementRank
    statementQualifiers : List Qualifier
    statementReferences : List ReferenceBlock
open Statement public

record Sitelink : Set where
  constructor sitelink
  field
    sitelinkSite : String
    sitelinkPage : String
open Sitelink public

record EntitySitelink : Set where
  constructor entitySitelink
  field
    sitelinkItem : Id.ItemId
    entityLink : Sitelink
open EntitySitelink public

record EntitySnapshot : Set where
  constructor entitySnapshot
  field
    snapshotItem : Id.ItemId
    snapshotLabels : List (String × String)
    snapshotStatements : List Statement
    snapshotSitelinks : List EntitySitelink
    snapshotReference : String
    snapshotContentHash : String
open EntitySnapshot public

-- Open-world and rank boundaries inherited from the current DASHI bridge.
data SomeValueEqualsNoValue : Set where
data NoValueEqualsStatementAbsent : Set where
data PreferredRankMeansDashiTruth : Set where

someValueIsNotNoValue : SomeValueEqualsNoValue → ⊥
someValueIsNotNoValue ()

noValueIsNotStatementAbsence : NoValueEqualsStatementAbsent → ⊥
noValueIsNotStatementAbsence ()

preferredRankDoesNotMeanDashiTruth : PreferredRankMeansDashiTruth → ⊥
preferredRankDoesNotMeanDashiTruth ()

record NativeStatementBoundary : Set where
  constructor native-statement-boundary
  field
    someValueDistinctFromNoValue : Bool
    noValueDistinctFromAbsence : Bool
    rankIsEpistemicTruth : Bool
    qualifiersAndReferencesRetainedNatively : Bool

canonicalNativeStatementBoundary : NativeStatementBoundary
canonicalNativeStatementBoundary =
  native-statement-boundary true true false true
