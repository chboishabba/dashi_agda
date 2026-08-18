module DASHI.Ontology.WikidataBFOMappingInferenceLatticeExact where

------------------------------------------------------------------------
-- BFO / WIKIDATA MAPPING STRENGTH IS QUERY-INDEXED, NOT ONE TOTAL ORDER
--
-- The live Wikidata BFO mapping surface uses at least three distinct links:
--   P12602 : BFO class identifier
--   P2888  : exact match URL
--   P1709  : equivalent class
-- together with ordinary Wikidata structural edges such as P279.
--
-- The important theorem is not merely that the names differ.  Their inference
-- licences differ, and the resulting information order is query-indexed.
-- In particular P2888 and P1709 are incomparable in this deliberately narrow
-- contract: one supplies semantic-interchange evidence and the other supplies
-- class-equivalence evidence.  Neither by property type alone supplies a
-- disjointness-transport theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Ontology.WikidataBFOEntityScopeExact as Scope

------------------------------------------------------------------------
-- A reusable licence profile over the currently distinguished query language.
------------------------------------------------------------------------

record LicenceProfile : Set where
  constructor licenceProfile
  field
    identifierLookup : Bool
    semanticInterchange : Bool
    classEquivalence : Bool
    subclassReasoning : Bool
    disjointnessTransport : Bool

open LicenceProfile public

profile : Scope.BFOLinkKind → LicenceProfile
profile Scope.p12602BFOClassIdentifier =
  licenceProfile true false false false false
profile Scope.p2888ExactMatch =
  licenceProfile false true false false false
profile Scope.p1709EquivalentClass =
  licenceProfile false false true false false
profile Scope.p279Subclass =
  licenceProfile false false false true false

------------------------------------------------------------------------
-- Query-specific witnesses of incomparability.
------------------------------------------------------------------------

p2888HasInterchangeWhereP1709DoesNot :
  LicenceProfile.semanticInterchange (profile Scope.p2888ExactMatch) ≡ true
  × LicenceProfile.semanticInterchange (profile Scope.p1709EquivalentClass) ≡ false
p2888HasInterchangeWhereP1709DoesNot = refl , refl

p1709HasClassEquivalenceWhereP2888DoesNot :
  LicenceProfile.classEquivalence (profile Scope.p1709EquivalentClass) ≡ true
  × LicenceProfile.classEquivalence (profile Scope.p2888ExactMatch) ≡ false
p1709HasClassEquivalenceWhereP2888DoesNot = refl , refl

------------------------------------------------------------------------
-- No single property supplies the full class-algebra/disjointness language.
------------------------------------------------------------------------

record FullClassAlgebraLicence (kind : Scope.BFOLinkKind) : Set where
  constructor fullClassAlgebraLicence
  field
    hasIdentifier : LicenceProfile.identifierLookup (profile kind) ≡ true
    hasInterchange : LicenceProfile.semanticInterchange (profile kind) ≡ true
    hasEquivalence : LicenceProfile.classEquivalence (profile kind) ≡ true
    hasSubclass : LicenceProfile.subclassReasoning (profile kind) ≡ true
    hasDisjointnessTransport : LicenceProfile.disjointnessTransport (profile kind) ≡ true

noSingleLinkHasFullClassAlgebraLicence :
  (kind : Scope.BFOLinkKind) → FullClassAlgebraLicence kind → ⊥
noSingleLinkHasFullClassAlgebraLicence Scope.p12602BFOClassIdentifier licence with
  FullClassAlgebraLicence.hasInterchange licence
... | ()
noSingleLinkHasFullClassAlgebraLicence Scope.p2888ExactMatch licence with
  FullClassAlgebraLicence.hasIdentifier licence
... | ()
noSingleLinkHasFullClassAlgebraLicence Scope.p1709EquivalentClass licence with
  FullClassAlgebraLicence.hasIdentifier licence
... | ()
noSingleLinkHasFullClassAlgebraLicence Scope.p279Subclass licence with
  FullClassAlgebraLicence.hasIdentifier licence
... | ()

------------------------------------------------------------------------
-- Composite mappings can accumulate licences without collapsing provenance.
------------------------------------------------------------------------

record CompositeBFOMapping : Set where
  constructor compositeBFOMapping
  field
    hasP12602 : Bool
    hasP2888 : Bool
    hasP1709 : Bool
    hasP279 : Bool
    hasExplicitDisjointnessTransportProof : Bool

open CompositeBFOMapping public

identifierAndExactMatchStillDoNotMintClassEquivalence :
  CompositeBFOMapping
identifierAndExactMatchStillDoNotMintClassEquivalence =
  compositeBFOMapping true true false false false

fullStructuralPacketRequiresExplicitTransport :
  CompositeBFOMapping
fullStructuralPacketRequiresExplicitTransport =
  compositeBFOMapping true true true true false

record MappingInferenceBoundary : Set where
  constructor mappingInferenceBoundary
  field
    identifierEqualsExactMatch : Bool
    exactMatchEqualsEquivalentClass : Bool
    subclassEqualsEquivalentClass : Bool
    mappingStrengthIsOneTotalOrder : Bool
    propertyPresenceMintsDisjointnessTransport : Bool
    inferenceLicenceIsQueryIndexed : Bool
    compositeEvidencePreservesPropertyProvenance : Bool

canonicalMappingInferenceBoundary : MappingInferenceBoundary
canonicalMappingInferenceBoundary =
  mappingInferenceBoundary false false false false false true true
