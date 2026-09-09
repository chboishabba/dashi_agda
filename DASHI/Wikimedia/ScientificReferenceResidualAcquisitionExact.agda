module DASHI.Wikimedia.ScientificReferenceResidualAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search
import DASHI.Wikimedia.ScientificReferenceEntityAtlasExact as Atlas

------------------------------------------------------------------------
-- SCIENTIFIC REFERENCE RESIDUAL -> ACQUISITION DEMAND
--
-- This is a consumer-side descriptor for unresolved scientific-reference
-- identity/provenance coordinates.  It deliberately does not import #823-only
-- IntrospectiveProofLoopExact while that owner is unmerged.  After #823 lands,
-- each demand can be welded definitionally to ConsumerDefectSourceDemand.
------------------------------------------------------------------------

data ScientificReferenceMissingCoordinate : Set where
  missingEntityIdentity : ScientificReferenceMissingCoordinate
  samePersonUnresolved : ScientificReferenceMissingCoordinate
  publicationIdentityUnresolved : ScientificReferenceMissingCoordinate
  sourceLocatorUnresolved : ScientificReferenceMissingCoordinate
  sourceCoverageUnresolved : ScientificReferenceMissingCoordinate

producerForReferenceCoordinate :
  ScientificReferenceMissingCoordinate → Search.ProducerClass
producerForReferenceCoordinate missingEntityIdentity = Search.attributionProducer
producerForReferenceCoordinate samePersonUnresolved = Search.identityProducer
producerForReferenceCoordinate publicationIdentityUnresolved = Search.identityProducer
producerForReferenceCoordinate sourceLocatorUnresolved = Search.exactCitedAuthorityProducer
producerForReferenceCoordinate sourceCoverageUnresolved = Search.empiricalEvidenceProducer

record ScientificReferenceResidual : Set where
  constructor scientific-reference-residual
  field
    referenceEntity : Atlas.ScientificReferenceEntity
    consumerReference : String
    missingCoordinate : ScientificReferenceMissingCoordinate
    residualReference : String
open ScientificReferenceResidual public

record ScientificReferenceAcquisitionDemand (residual : ScientificReferenceResidual) : Set where
  constructor scientific-reference-acquisition-demand
  field
    producer : Search.ProducerClass
    producerMatchesResidual : producer ≡ producerForReferenceCoordinate (missingCoordinate residual)
    queryScopeReference : String
    sameObjectRequirementReference : String
    demandReference : String
open ScientificReferenceAcquisitionDemand public

-- A retrieval result does not pay the coordinate merely by existing.  Payment
-- requires a later same-object/source admission and recomputation of the exact
-- residual.
data RetrievalResultPaysReferenceResidual : Set where
data QidCandidatePaysSamePersonResidual : Set where
data DifferentReferenceResidualPaysThisResidual : Set where

retrievalDoesNotPayResidualByExistence : RetrievalResultPaysReferenceResidual → ⊥
retrievalDoesNotPayResidualByExistence ()

qidCandidateDoesNotPaySamePersonResidual : QidCandidatePaysSamePersonResidual → ⊥
qidCandidateDoesNotPaySamePersonResidual ()

otherResidualPaymentDoesNotPayThisResidual : DifferentReferenceResidualPaysThisResidual → ⊥
otherResidualPaymentDoesNotPayThisResidual ()

-- Concrete current unresolved examples.
robertKohnIdentityResidual : ScientificReferenceResidual
robertKohnIdentityResidual =
  scientific-reference-residual
    Atlas.robertKohn
    "CKN / Navier-Stokes citation identity consumer"
    samePersonUnresolved
    "resolve the cited Robert V. Kohn to a source-backed Wikidata entity without name-only matching"

robertKohnIdentityDemand : ScientificReferenceAcquisitionDemand robertKohnIdentityResidual
robertKohnIdentityDemand =
  scientific-reference-acquisition-demand
    Search.identityProducer
    refl
    "search author metadata, institutional profiles, DOI metadata and Wikidata candidates"
    "candidate must be the Robert V. Kohn who coauthored the cited CKN paper"
    "scientific-reference residual-bound acquisition: Robert V. Kohn"

tadeuszBalabanIdentityResidual : ScientificReferenceResidual
tadeuszBalabanIdentityResidual =
  scientific-reference-residual
    Atlas.tadeuszBalaban
    "Balaban Yang-Mills source attribution consumer"
    samePersonUnresolved
    "resolve Tadeusz Balaban source identity without conflating namesakes"

tadeuszBalabanIdentityDemand : ScientificReferenceAcquisitionDemand tadeuszBalabanIdentityResidual
tadeuszBalabanIdentityDemand =
  scientific-reference-acquisition-demand
    Search.identityProducer
    refl
    "search publication metadata, institutional authority records and Wikidata candidates"
    "candidate must be the lattice gauge theory author cited by the Balaban source modules"
    "scientific-reference residual-bound acquisition: Tadeusz Balaban"

record ScientificReferenceResidualBoundary : Set where
  constructor scientific-reference-residual-boundary
  field
    acquisitionIsIndexedByExactResidual : Bool
    producerIsDerivedFromMissingCoordinate : Bool
    retrievalEqualsPayment : Bool
    candidateQidEqualsSamePersonProof : Bool
    oneResidualPaymentClosesOtherResiduals : Bool
    pending823WeldExplicit : Bool

canonicalScientificReferenceResidualBoundary : ScientificReferenceResidualBoundary
canonicalScientificReferenceResidualBoundary =
  scientific-reference-residual-boundary true true false false false true
