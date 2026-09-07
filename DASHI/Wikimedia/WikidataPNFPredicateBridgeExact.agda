module DASHI.Wikimedia.WikidataPNFPredicateBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.NativeStatementExact as WD
import DASHI.Wikimedia.SourceProvenanceExact as Source

------------------------------------------------------------------------
-- WIKIDATA PROPERTY -> PNF PREDICATE ALIGNMENT
--
-- A Wikidata property is highly compatible with PNF's predicate-symbol role,
-- but property identity alone does not choose a DASHI logical/inferential role.
-- The mapping therefore requires an explicit reviewed/source-bearing alignment.
------------------------------------------------------------------------

record PropertyPredicateAlignment : Set where
  constructor propertyPredicateAlignment
  field
    property : Id.PropertyId
    predicateRole : PNF.PredicateRole
    predicateDomain : String
    predicateReading : String
    alignmentEvidence : Source.SourceReceipt
    alignmentReference : String
open PropertyPredicateAlignment public

asPredicateAtom : PropertyPredicateAlignment → PNF.PredicateAtom
asPredicateAtom alignment =
  PNF.predicateAtom
    (Id.rawPropertyId (property alignment))
    (predicateRole alignment)
    (predicateDomain alignment)
    (predicateReading alignment)

record StatementPredicateBridge (statement : WD.Statement) : Set where
  constructor statement-predicate-bridge
  field
    alignment : PropertyPredicateAlignment
    propertyMatches : WD.property statement ≡ property alignment
    bridgeReference : String
open StatementPredicateBridge public

statementPredicateAtom :
  {statement : WD.Statement} →
  StatementPredicateBridge statement →
  PNF.PredicateAtom
statementPredicateAtom bridge = asPredicateAtom (alignment bridge)

statementPredicateNamePreserved :
  {statement : WD.Statement} →
  (bridge : StatementPredicateBridge statement) →
  PNF.predicateName (statementPredicateAtom bridge)
  ≡ Id.rawPropertyId (WD.property statement)
statementPredicateNamePreserved {statement} (statement-predicate-bridge alignment refl ref) = refl

-- Property metadata and PNF inferential force remain orthogonal.
data PropertyIdDeterminesInferentialForce : Set where
data PropertyIdMakesCausalClaim : Set where
data WikidataStatementCreatesNormativeAuthority : Set where
data WikidataRankCreatesPNFTruth : Set where

propertyIdDoesNotDetermineInferentialForce : PropertyIdDeterminesInferentialForce → ⊥
propertyIdDoesNotDetermineInferentialForce ()

propertyIdDoesNotCreateCausality : PropertyIdMakesCausalClaim → ⊥
propertyIdDoesNotCreateCausality ()

wikidataStatementDoesNotCreateNormativeAuthority :
  WikidataStatementCreatesNormativeAuthority → ⊥
wikidataStatementDoesNotCreateNormativeAuthority ()

wikidataRankDoesNotCreatePNFTruth : WikidataRankCreatesPNFTruth → ⊥
wikidataRankDoesNotCreatePNFTruth ()

record WikidataPNFBoundary : Set where
  constructor wikidata-pnf-boundary
  field
    propertyCanSupplyPredicateSymbol : Bool
    propertyNeedsRoleReadingDomainAlignment : Bool
    propertyIdentityDeterminesInferentialForce : Bool
    propertyIdentityCreatesCausality : Bool
    statementCreatesNormativeAuthority : Bool

canonicalWikidataPNFBoundary : WikidataPNFBoundary
canonicalWikidataPNFBoundary =
  wikidata-pnf-boundary true true false false false
