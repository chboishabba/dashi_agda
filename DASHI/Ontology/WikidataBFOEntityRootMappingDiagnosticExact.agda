module DASHI.Ontology.WikidataBFOEntityRootMappingDiagnosticExact where

------------------------------------------------------------------------
-- Q35120 / Q136433660 BFO ROOT MAPPING DIAGNOSTIC
--
-- Current Wikidata surfaces contain two relevant facts that must not be
-- silently normalized into one mapping:
--
--   * P12602 documentation historically/currently presents Q35120 -> 0000001
--     as a BFO-class-ID example;
--   * Q136433660 is the BFO Entity-facing item and is modelled as a subclass
--     of Q35120, with the BFO continuant/occurrent partition local to it.
--
-- This is a mapping-attribution problem, not by itself an ontology
-- contradiction.  The correct result of a packet carrying both candidates is
-- "ambiguous/unresolved until an explicit mapping decision", not an invented
-- equivalence and not a refutation of either ontology.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Ontology.WikidataBFOEntityScopeExact as Scope

------------------------------------------------------------------------
-- Candidate roots and the provenance layer that supplied each observation.
------------------------------------------------------------------------

data CandidateRoot : Set where
  q35120Candidate : CandidateRoot
  q136433660Candidate : CandidateRoot

data MappingProvenanceLayer : Set where
  bfoSourceLayer : MappingProvenanceLayer
  wikidataPropertyDocumentationLayer : MappingProvenanceLayer
  wikidataItemStructureLayer : MappingProvenanceLayer
  crossOntologyAlignmentLayer : MappingProvenanceLayer

data DiagnosticState : Set where
  verified : DiagnosticState
  ambiguous : DiagnosticState
  unresolved : DiagnosticState
  refuted : DiagnosticState

record RootMappingPacket : Set where
  constructor rootMappingPacket
  field
    bfoIdentifier : String
    q35120CandidateActive : Bool
    q136433660CandidateActive : Bool
    q136433660SubclassQ35120Observed : Bool
    explicitSemanticRootDecision : Bool
    q35120LinkKind : Scope.BFOLinkKind
    q136433660LinkKind : Scope.BFOLinkKind
    packetProvenance : String

open RootMappingPacket public

canonicalRootMappingPacket : RootMappingPacket
canonicalRootMappingPacket =
  rootMappingPacket
    "0000001"
    true
    true
    true
    false
    Scope.p12602BFOClassIdentifier
    Scope.p12602BFOClassIdentifier
    "P12602 example + current BFO-specific Q136433660 item structure; 2026-08-19"

------------------------------------------------------------------------
-- Unique resolution requires an explicit choice and exactly one active root.
------------------------------------------------------------------------

data UniqueResolvedRoot (packet : RootMappingPacket) : Set where
  chooseQ35120 :
    q35120CandidateActive packet ≡ true →
    q136433660CandidateActive packet ≡ false →
    explicitSemanticRootDecision packet ≡ true →
    UniqueResolvedRoot packet
  chooseQ136433660 :
    q35120CandidateActive packet ≡ false →
    q136433660CandidateActive packet ≡ true →
    explicitSemanticRootDecision packet ≡ true →
    UniqueResolvedRoot packet

canonicalPacketHasNoUniqueResolvedRoot :
  UniqueResolvedRoot canonicalRootMappingPacket → ⊥
canonicalPacketHasNoUniqueResolvedRoot (chooseQ35120 _ () _)
canonicalPacketHasNoUniqueResolvedRoot (chooseQ136433660 () _ _)

------------------------------------------------------------------------
-- Layered attribution: ambiguity is located without manufacturing conflict.
------------------------------------------------------------------------

record LayeredRootDiagnostic : Set where
  constructor layeredRootDiagnostic
  field
    sourceOntologyStatus : DiagnosticState
    transcriptionStatus : DiagnosticState
    alignmentStatus : DiagnosticState
    targetGraphStatus : DiagnosticState
    finalStatus : DiagnosticState

open LayeredRootDiagnostic public

canonicalLayeredRootDiagnostic : LayeredRootDiagnostic
canonicalLayeredRootDiagnostic =
  layeredRootDiagnostic
    verified
    ambiguous
    unresolved
    verified
    unresolved

transcriptionAmbiguityDoesNotBecomeSourceRefutation :
  sourceOntologyStatus canonicalLayeredRootDiagnostic ≡ verified
transcriptionAmbiguityDoesNotBecomeSourceRefutation = refl

ambiguousPacketRemainsUnresolved :
  finalStatus canonicalLayeredRootDiagnostic ≡ unresolved
ambiguousPacketRemainsUnresolved = refl

------------------------------------------------------------------------
-- Identifier-level agreement is weaker than semantic-root resolution.
------------------------------------------------------------------------

record IdentifierAgreement : Set where
  constructor identifierAgreement
  field
    identifier : String
    leftUsesIdentifier : Bool
    rightUsesIdentifier : Bool

canonicalIdentifierAgreement : IdentifierAgreement
canonicalIdentifierAgreement =
  identifierAgreement "0000001" true true

identifierAgreementDoesNotResolveRoot :
  UniqueResolvedRoot canonicalRootMappingPacket → ⊥
identifierAgreementDoesNotResolveRoot = canonicalPacketHasNoUniqueResolvedRoot

------------------------------------------------------------------------
-- Boundary exported to the working-group regression.
------------------------------------------------------------------------

record EntityRootMappingDiagnosticBoundary : Set where
  constructor entityRootMappingDiagnosticBoundary
  field
    twoCandidatesMeanEquivalent : Bool
    sameIdentifierMeansSameWikidataItem : Bool
    transcriptionAmbiguityRefutesBFO : Bool
    unresolvedAlignmentRefutesWikidata : Bool
    ambiguityRequiresReview : Bool
    preserveSourceTranscriptionAlignmentTargetLayers : Bool

canonicalEntityRootMappingDiagnosticBoundary :
  EntityRootMappingDiagnosticBoundary
canonicalEntityRootMappingDiagnosticBoundary =
  entityRootMappingDiagnosticBoundary false false false false true true
