module DASHI.Wikimedia.NativeConcreteQidGraphProjectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Ontology.LeanWikidataExistingContentAudit as Audit
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.NativeStatementExact as WD

------------------------------------------------------------------------
-- NATIVE WIKIMEDIA -> EXECUTABLE P31/P279/DISJOINT GRAPH PROJECTION
--
-- Aristotle archive recheck, 7 Sep 2026:
--   RequestProject.Engine.KB stores exactly items / sub(P279) / inst(P31) /
--   disj plus level metadata.  RequestProject.PropertyEngine.PKB is a separate
--   richer property layer.  Therefore this adapter is intentionally lossy:
--   arbitrary native statements (for example P710 participant) remain in the
--   native/PNF carrier and are not forced into the ontology kernel.
------------------------------------------------------------------------

p31 : Id.PropertyId
p31 = Id.propertyId "P31"

p279 : Id.PropertyId
p279 = Id.propertyId "P279"

data KernelRelationKind : Set where
  instanceRelation
  subclassRelation
  : KernelRelationKind

propertyFor : KernelRelationKind → Id.PropertyId
propertyFor instanceRelation = p31
propertyFor subclassRelation = p279

record NativeKernelFact : Set where
  constructor native-kernel-fact
  field
    relationKind : KernelRelationKind
    sourceStatement : WD.Statement
    subjectItem : Id.ItemId
    objectItem : Id.ItemId
    subjectMatches : WD.statementSubject sourceStatement ≡ Id.itemEntity subjectItem
    objectMatches : WD.mainsnak sourceStatement ≡ WD.valueSnak (WD.entityValue (Id.itemEntity objectItem))
    propertyMatches : WD.statementProperty sourceStatement ≡ propertyFor relationKind
    factReference : String
open NativeKernelFact public

record NativeDisjointFact : Set where
  constructor native-disjoint-fact
  field
    leftItem : Id.ItemId
    rightItem : Id.ItemId
    disjointReference : String
open NativeDisjointFact public

record NativeConcreteGraphCandidate : Set where
  constructor native-concrete-graph-candidate
  field
    graphIdentifier : String
    graphItems : List Id.ItemId
    kernelFacts : List NativeKernelFact
    disjointFacts : List NativeDisjointFact
    provenanceReferences : List String
    projectionSourceReference : String
open NativeConcreteGraphCandidate public

itemReferences : List Id.ItemId → List String
itemReferences [] = []
itemReferences (q ∷ qs) = Id.rawItemId q ∷ itemReferences qs

instanceFactReferences : List NativeKernelFact → List String
instanceFactReferences [] = []
instanceFactReferences (fact ∷ rest) with relationKind fact
... | instanceRelation = factReference fact ∷ instanceFactReferences rest
... | subclassRelation = instanceFactReferences rest

subclassFactReferences : List NativeKernelFact → List String
subclassFactReferences [] = []
subclassFactReferences (fact ∷ rest) with relationKind fact
... | instanceRelation = subclassFactReferences rest
... | subclassRelation = factReference fact ∷ subclassFactReferences rest

disjointFactReferences : List NativeDisjointFact → List String
disjointFactReferences [] = []
disjointFactReferences (fact ∷ rest) = disjointReference fact ∷ disjointFactReferences rest

------------------------------------------------------------------------
-- Content-addressing is an explicit promotion gate.
--
-- A native candidate can be assembled from revision-pinned source observations
-- before its exact graph serialization/hash is available.  It becomes eligible
-- for the existing James/Aristotle execution receipt only after a producer
-- supplies a verified hash receipt for the exact projected graph.
------------------------------------------------------------------------

record ContentAddressReceipt (candidate : NativeConcreteGraphCandidate) : Set where
  constructor content-address-receipt
  field
    graphSha256 : String
    hashSourceReference : String
    hashVerified : Bool
    hashVerifiedIsTrue : hashVerified ≡ true
open ContentAddressReceipt public

asConcreteQidGraphAdapter :
  (candidate : NativeConcreteGraphCandidate) →
  ContentAddressReceipt candidate →
  Audit.ConcreteQidGraphAdapter
asConcreteQidGraphAdapter candidate receipt =
  Audit.concreteQidGraphAdapter
    (graphIdentifier candidate)
    (graphSha256 receipt)
    (itemReferences (graphItems candidate))
    (instanceFactReferences (kernelFacts candidate))
    (subclassFactReferences (kernelFacts candidate))
    (disjointFactReferences (disjointFacts candidate))
    (provenanceReferences candidate)

adapterHashPreserved :
  (candidate : NativeConcreteGraphCandidate) →
  (receipt : ContentAddressReceipt candidate) →
  Audit.graphSha256 (asConcreteQidGraphAdapter candidate receipt) ≡ graphSha256 receipt
adapterHashPreserved candidate receipt = refl

adapterP31ProjectionPreserved :
  (candidate : NativeConcreteGraphCandidate) →
  (receipt : ContentAddressReceipt candidate) →
  Audit.p31FactReferences (asConcreteQidGraphAdapter candidate receipt)
  ≡ instanceFactReferences (kernelFacts candidate)
adapterP31ProjectionPreserved candidate receipt = refl

adapterP279ProjectionPreserved :
  (candidate : NativeConcreteGraphCandidate) →
  (receipt : ContentAddressReceipt candidate) →
  Audit.p279FactReferences (asConcreteQidGraphAdapter candidate receipt)
  ≡ subclassFactReferences (kernelFacts candidate)
adapterP279ProjectionPreserved candidate receipt = refl

------------------------------------------------------------------------
-- Loss / authority firewalls.
------------------------------------------------------------------------

data ArbitraryNativePropertyIsKernelFact : Set where
data ProjectionIsNativeSourceOfTruth : Set where
data UnhashedCandidateIsKernelExecutionReceipt : Set where
data P710ParticipantAutomaticallyBecomesP31OrP279 : Set where

arbitraryPropertyDoesNotBecomeKernelFact : ArbitraryNativePropertyIsKernelFact → ⊥
arbitraryPropertyDoesNotBecomeKernelFact ()

projectionDoesNotBecomeNativeAuthority : ProjectionIsNativeSourceOfTruth → ⊥
projectionDoesNotBecomeNativeAuthority ()

unhashedCandidateDoesNotBecomeExecutionReceipt : UnhashedCandidateIsKernelExecutionReceipt → ⊥
unhashedCandidateDoesNotBecomeExecutionReceipt ()

participantDoesNotBecomeOntologyEdge : P710ParticipantAutomaticallyBecomesP31OrP279 → ⊥
participantDoesNotBecomeOntologyEdge ()

record NativeConcreteProjectionBoundary : Set where
  constructor native-concrete-projection-boundary
  field
    p31AndP279ProjectToKernel : Bool
    arbitraryPropertiesProjectToKernel : Bool
    projectionRetainsWholeNativeStatementLanguage : Bool
    exactGraphHashRequiredBeforeKernelExecution : Bool

canonicalNativeConcreteProjectionBoundary : NativeConcreteProjectionBoundary
canonicalNativeConcreteProjectionBoundary =
  native-concrete-projection-boundary true false false true
