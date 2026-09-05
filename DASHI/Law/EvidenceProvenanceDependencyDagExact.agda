module DASHI.Law.EvidenceProvenanceDependencyDagExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Multiple records are not automatically multiple independent producers.
------------------------------------------------------------------------

data EvidenceNode : Set where
  officerStatement bodyCamera agencyDatabase agencySummary independentWitness medicalRecord : EvidenceNode

data ProvenanceRelation : Set where
  derivesFrom independentOf : ProvenanceRelation

record ProvenanceEdge : Set where
  constructor provenanceEdge
  field
    child parent : EvidenceNode
    relation : ProvenanceRelation
    provenanceReference : String

open ProvenanceEdge public

record SharedUltimateProducer : Set where
  constructor sharedUltimateProducer
  field
    leftReceipt rightReceipt ultimateProducer : EvidenceNode
    leftDerivesFromUltimate : ProvenanceEdge
    rightDerivesFromUltimate : ProvenanceEdge
    dependencyReference : String

open SharedUltimateProducer public

record IndependentCorroboration : Set where
  constructor independentCorroboration
  field
    firstReceipt secondReceipt : EvidenceNode
    independenceReceipt : ProvenanceEdge
    corroborationReference : String

open IndependentCorroboration public

------------------------------------------------------------------------
-- Concrete institutional dependency chain.
------------------------------------------------------------------------

officerToDatabase : ProvenanceEdge
officerToDatabase = provenanceEdge
  agencyDatabase officerStatement derivesFrom
  "agency database populated from officer-originated encounter record"

officerToSummary : ProvenanceEdge
officerToSummary = provenanceEdge
  agencySummary officerStatement derivesFrom
  "agency summary ultimately derived from officer-originated encounter record"

canonicalSharedProducer : SharedUltimateProducer
canonicalSharedProducer = sharedUltimateProducer
  agencyDatabase agencySummary officerStatement
  officerToDatabase officerToSummary
  "two institutional outputs share one ultimate producer"

------------------------------------------------------------------------
-- Count and independence are separate coordinates.
------------------------------------------------------------------------

data ReceiptMultiplicity : Set where
  oneReceipt twoReceipts threeOrMoreReceipts : ReceiptMultiplicity

data IndependenceState : Set where
  independent dependent independenceUnresolved : IndependenceState

record CorroborationSurface : Set where
  constructor corroborationSurface
  field
    multiplicity : ReceiptMultiplicity
    independence : IndependenceState
    surfaceReference : String

open CorroborationSurface public

multipleButDependent : CorroborationSurface
multipleButDependent = corroborationSurface twoReceipts dependent
  "multiple reports can remain one-source corroboration"

record ProvenanceDagBoundary : Set where
  constructor provenanceDagBoundary
  field
    multipleReceiptsAutomaticallyIndependent : Bool
    multipleReceiptsAutomaticallyIndependentIsFalse :
      multipleReceiptsAutomaticallyIndependent ≡ false
    sharedUltimateProducerCountsAsIndependentCorroboration : Bool
    sharedUltimateProducerCountsAsIndependentCorroborationIsFalse :
      sharedUltimateProducerCountsAsIndependentCorroboration ≡ false
    derivedInstitutionalSummaryCreatesNewUnderlyingObservation : Bool
    derivedInstitutionalSummaryCreatesNewUnderlyingObservationIsFalse :
      derivedInstitutionalSummaryCreatesNewUnderlyingObservation ≡ false

canonicalProvenanceDagBoundary : ProvenanceDagBoundary
canonicalProvenanceDagBoundary =
  provenanceDagBoundary false refl false refl false refl

------------------------------------------------------------------------
-- BIDI: a consumer requiring independent corroboration reopens provenance,
-- even when raw receipt multiplicity is already greater than one.
------------------------------------------------------------------------

data ProvenanceConsumer : Set where
  existenceOfRecord independentCorroborationConsumer : ProvenanceConsumer

data ProvenanceObligation : Set where
  anyReceiptReceipt independentProducerReceipt : ProvenanceObligation

reverseProvenance : ProvenanceConsumer → ProvenanceObligation
reverseProvenance existenceOfRecord = anyReceiptReceipt
reverseProvenance independentCorroborationConsumer = independentProducerReceipt

independenceConsumerRequiresProducerReceipt :
  reverseProvenance independentCorroborationConsumer ≡ independentProducerReceipt
independenceConsumerRequiresProducerReceipt = refl
