module DASHI.Wikimedia.ConceptEntityAlignmentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.SourceProvenanceExact as Source

------------------------------------------------------------------------
-- DASHI CONCEPT <-> WIKIMEDIA ENTITY ALIGNMENT
--
-- QIDs are external identity handles.  A DASHI concept may be linked to an
-- entity under typed evidence; the link does not identify the two semantic
-- objects definitionally.
------------------------------------------------------------------------

record DashiConceptRef : Set where
  constructor dashiConceptRef
  field
    conceptReference : String
    conceptReading : String
open DashiConceptRef public

data AlignmentKind : Set where
  candidateAlignment : AlignmentKind
  directIdentifierEvidence : AlignmentKind
  sitelinkAssociation : AlignmentKind
  externalIdentifierMatch : AlignmentKind
  exactMatchRelation : AlignmentKind
  equivalentClassRelation : AlignmentKind
  subclassRelation : AlignmentKind
  lexicalSenseCandidate : AlignmentKind
  reviewedSemanticAlignment : AlignmentKind

data AlignmentStatus : Set where
  candidate : AlignmentStatus
  sourceBacked : AlignmentStatus
  ambiguous : AlignmentStatus
  rejected : AlignmentStatus
  reviewedAccepted : AlignmentStatus

record ConceptEntityAlignment : Set where
  constructor conceptEntityAlignment
  field
    concept : DashiConceptRef
    entity : Id.EntityId
    kind : AlignmentKind
    status : AlignmentStatus
    evidence : List Source.SourceReceipt
    scopeReference : String
    alignmentReference : String
open ConceptEntityAlignment public

-- Existing Wikidata working-group non-collapse rules become native invariants.
data IdentifierAgreementIsSemanticEquivalence : Set where
data LabelEqualityIsOntologyIdentity : Set where
data SitelinkIsReviewedSemanticAlignment : Set where
data SubclassIsEquivalentClass : Set where

identifierAgreementDoesNotForceSemanticEquivalence :
  IdentifierAgreementIsSemanticEquivalence → ⊥
identifierAgreementDoesNotForceSemanticEquivalence ()

labelEqualityDoesNotForceOntologyIdentity : LabelEqualityIsOntologyIdentity → ⊥
labelEqualityDoesNotForceOntologyIdentity ()

sitelinkDoesNotForceReviewedSemanticAlignment : SitelinkIsReviewedSemanticAlignment → ⊥
sitelinkDoesNotForceReviewedSemanticAlignment ()

subclassDoesNotBecomeEquivalentClass : SubclassIsEquivalentClass → ⊥
subclassDoesNotBecomeEquivalentClass ()

record ConceptEntityAlignmentBoundary : Set where
  constructor concept-entity-alignment-boundary
  field
    qidStoredAsExternalHandle : Bool
    labelEqualityCreatesIdentity : Bool
    sitelinkCreatesSemanticEquivalence : Bool
    relationRolesRemainDistinct : Bool
    alignmentEvidenceCarriesSourceLayer : Bool

canonicalConceptEntityAlignmentBoundary : ConceptEntityAlignmentBoundary
canonicalConceptEntityAlignmentBoundary =
  concept-entity-alignment-boundary true false false true true
