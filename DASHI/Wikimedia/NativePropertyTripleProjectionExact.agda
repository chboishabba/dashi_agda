module DASHI.Wikimedia.NativePropertyTripleProjectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.NativeStatementExact as WD
import DASHI.Wikimedia.AristotleNativeModelSourceExact as Aristotle

------------------------------------------------------------------------
-- NATIVE STATEMENT -> GENERAL ITEM-VALUED PROPERTY TRIPLE
--
-- Aristotle RequestProject.PropertyEngine.PKB stores general property facts as
-- `(Pid × Qid × Qid)` in a layer distinct from Engine.KB's P31/P279 ontology
-- edges.  This bridge mirrors that separation without pretending every native
-- Wikidata value is an item-valued triple.
------------------------------------------------------------------------

record NativeItemPropertyFact : Set where
  constructor native-item-property-fact
  field
    sourceStatement : WD.Statement
    propertyId : Id.PropertyId
    subjectItem : Id.ItemId
    objectItem : Id.ItemId
    propertyMatches : WD.statementProperty sourceStatement ≡ propertyId
    subjectMatches : WD.statementSubject sourceStatement ≡ Id.itemEntity subjectItem
    objectMatches : WD.mainsnak sourceStatement ≡ WD.valueSnak (WD.entityValue (Id.itemEntity objectItem))
    factReference : String
open NativeItemPropertyFact public

record PropertyTriple : Set where
  constructor property-triple
  field
    tripleProperty : String
    tripleSubject : String
    tripleObject : String
    tripleReference : String
open PropertyTriple public

asPropertyTriple : NativeItemPropertyFact → PropertyTriple
asPropertyTriple fact =
  property-triple
    (Id.rawPropertyId (propertyId fact))
    (Id.rawItemId (subjectItem fact))
    (Id.rawItemId (objectItem fact))
    (factReference fact)

propertyPreserved :
  (fact : NativeItemPropertyFact) →
  tripleProperty (asPropertyTriple fact) ≡ Id.rawPropertyId (propertyId fact)
propertyPreserved fact = refl

subjectPreserved :
  (fact : NativeItemPropertyFact) →
  tripleSubject (asPropertyTriple fact) ≡ Id.rawItemId (subjectItem fact)
subjectPreserved fact = refl

objectPreserved :
  (fact : NativeItemPropertyFact) →
  tripleObject (asPropertyTriple fact) ≡ Id.rawItemId (objectItem fact)
objectPreserved fact = refl

propertyEngineSourceContract : Aristotle.AristotleDeclarationContract
propertyEngineSourceContract = Aristotle.propertyEngineContract

------------------------------------------------------------------------
-- Loss boundary.
--
-- String/time/quantity/monolingual values, someValue/noValue, qualifiers,
-- references and rank all remain in the native carrier.  A general property
-- triple is therefore another consumer projection, not native source authority.
------------------------------------------------------------------------

data EveryNativeStatementIsItemTriple : Set where
data PropertyTripleRetainsQualifiersAndReferences : Set where
data PropertyTripleIsWholeNativeStatement : Set where

everyStatementDoesNotBecomeItemTriple : EveryNativeStatementIsItemTriple → ⊥
everyStatementDoesNotBecomeItemTriple ()

propertyTripleDoesNotRetainWholeContext : PropertyTripleRetainsQualifiersAndReferences → ⊥
propertyTripleDoesNotRetainWholeContext ()

propertyTripleDoesNotBecomeNativeStatement : PropertyTripleIsWholeNativeStatement → ⊥
propertyTripleDoesNotBecomeNativeStatement ()

record NativePropertyTripleBoundary : Set where
  constructor native-property-triple-boundary
  field
    itemValuedStatementsCanProject : Bool
    allNativeStatementsProject : Bool
    qualifiersReferencesRanksRetainedByTriple : Bool
    tripleIsNativeAuthority : Bool

canonicalNativePropertyTripleBoundary : NativePropertyTripleBoundary
canonicalNativePropertyTripleBoundary =
  native-property-triple-boundary true false false false
