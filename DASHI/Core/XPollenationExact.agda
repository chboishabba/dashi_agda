module DASHI.Core.XPollenationExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- GENERIC CROSS-DOMAIN XPOLLENATION ABI
--
-- xPollenation records typed external-identity relationships and the exact
-- provenance used to discover them.  It is a navigation/enrichment layer.
-- It never turns identifier adjacency, content identity, DA51 identity, or a
-- transport receipt into theorem/empirical/payment authority.
------------------------------------------------------------------------

data ExternalNamespace : Set where
  wikidataQid : ExternalNamespace
  chebi : ExternalNamespace
  rhea : ExternalNamespace
  uniprot : ExternalNamespace
  pdb : ExternalNamespace
  sabio : ExternalNamespace
  pubmed : ExternalNamespace
  doi : ExternalNamespace
  pubchem : ExternalNamespace
  oeis : ExternalNamespace
  da51 : ExternalNamespace
  customNamespace : String → ExternalNamespace

data RelationKind : Set where
  exactSameObject : RelationKind
  curatedCrossReference : RelationKind
  reactionParticipant : RelationKind
  catalysedBy : RelationKind
  proteinStructureOf : RelationKind
  kineticParameterFor : RelationKind
  measuredInAssay : RelationKind
  describedByPublication : RelationKind
  candidateNeighbour : RelationKind
  numericalCoincidence : RelationKind
  ontologyParent : RelationKind
  possibleSameObject : RelationKind
  wrongType : RelationKind
  negativeControl : RelationKind

data EdgeStatus : Set where
  discovered : EdgeStatus
  identityPaid : EdgeStatus
  contextPaid : EdgeStatus
  paymentEligible : EdgeStatus

record ExternalCoordinate : Set where
  constructor external-coordinate
  field
    namespace : ExternalNamespace
    identifier : String

open ExternalCoordinate public

record XPollenationEdge : Set where
  constructor xpollenation-edge
  field
    edgeId : String
    subject : ExternalCoordinate
    relation : RelationKind
    object : ExternalCoordinate
    sourceReference : String
    sourceRevision : String
    acquisitionReceipt : String
    status : EdgeStatus
    sameObjectClaimed : Bool
    sameObjectVerified : Bool
    contextEquivalent : Bool
    promotionAllowed : Bool

open XPollenationEdge public

record XPollenationNeighbourhood : Set where
  constructor xpollenation-neighbourhood
  field
    neighbourhoodId : String
    focus : ExternalCoordinate
    edges : List XPollenationEdge
    logicalArtifactRef : String
    contentDigest : String
    cid : String
    da51Address : String
    authority : String
    establishesProof : Bool
    establishesPayment : Bool

open XPollenationNeighbourhood public

record XPollenationBoundary : Set where
  constructor xpollenation-boundary
  field
    qidAdjacencyCreatesSameObject : Bool
    qidAdjacencyCreatesSameObjectIsFalse : qidAdjacencyCreatesSameObject ≡ false
    oeisMatchCreatesSemanticEquivalence : Bool
    oeisMatchCreatesSemanticEquivalenceIsFalse :
      oeisMatchCreatesSemanticEquivalence ≡ false
    cidCreatesSemanticIdentity : Bool
    cidCreatesSemanticIdentityIsFalse : cidCreatesSemanticIdentity ≡ false
    da51CreatesExternalIdentity : Bool
    da51CreatesExternalIdentityIsFalse : da51CreatesExternalIdentity ≡ false
    edgeCreatesProof : Bool
    edgeCreatesProofIsFalse : edgeCreatesProof ≡ false
    edgeCreatesConsumerPayment : Bool
    edgeCreatesConsumerPaymentIsFalse : edgeCreatesConsumerPayment ≡ false
    transportResolutionCreatesContextEquivalence : Bool
    transportResolutionCreatesContextEquivalenceIsFalse :
      transportResolutionCreatesContextEquivalence ≡ false

open XPollenationBoundary public

canonicalXPollenationBoundary : XPollenationBoundary
canonicalXPollenationBoundary =
  xpollenation-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

canonicalXPollenationReceipt : Receipt.GenericReceipt
canonicalXPollenationReceipt =
  Receipt.mkNonPromotingReceipt
    "generic xPollenation external-identity graph"
    "DASHI.Core.XPollenationExact"
    "typed external-coordinate edges with source revision, acquisition receipt, edge status and optional DA51/logical-artifact/CID coordinates"
    "provides one reusable navigation/enrichment ABI for Wikidata QID, ChEBI, Rhea, UniProt, PDB, SABIO, PMID, DOI, PubChem, OEIS and custom domains without inventing a second truth or storage system"
    "QID/OEIS adjacency is not semantic identity; CID is content identity only; DA51 is internal logical identity only; an xPollenation edge or transport receipt cannot create proof, context equivalence or consumer payment"
    "agda -i . DASHI/Core/XPollenationExact.agda"
