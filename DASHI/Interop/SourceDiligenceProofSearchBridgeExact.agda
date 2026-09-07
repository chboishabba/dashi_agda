module DASHI.Interop.SourceDiligenceProofSearchBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.EmpiricalSourceDiligenceAdmissionExact as Diligence
import DASHI.Core.SourceAcquisitionGeometryExact as Acquisition
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- SOURCE-DILIGENCE -> EXISTING PROOF-SEARCH BRIDGE
--
-- The repository already owns residual/search geometry in the legal/research
-- stack.  This module does not introduce a parallel residual algebra.  It only
-- names the source-diligence coordinate currently blocking a proposition and
-- maps that coordinate into the existing ProducerClass vocabulary.
------------------------------------------------------------------------

data SourceDiligenceGap : Set where
  missingSourceIdentity : SourceDiligenceGap
  primarySourceNotSearched : SourceDiligenceGap
  missingExactLocator : SourceDiligenceGap
  propositionSupportUnresolved : SourceDiligenceGap
  sameObjectUnresolved : SourceDiligenceGap
  temporalScopeUnresolved : SourceDiligenceGap
  coverageUnresolved : SourceDiligenceGap
  contradictionSearchOpen : SourceDiligenceGap
  interpretationBoundaryOpen : SourceDiligenceGap
  applicabilityOpen : SourceDiligenceGap
  authorityOpen : SourceDiligenceGap

producerForSourceDiligenceGap : SourceDiligenceGap → Search.ProducerClass
producerForSourceDiligenceGap missingSourceIdentity = Search.attributionProducer
producerForSourceDiligenceGap primarySourceNotSearched = Search.propositionSourceProducer
producerForSourceDiligenceGap missingExactLocator = Search.exactCitedAuthorityProducer
producerForSourceDiligenceGap propositionSupportUnresolved = Search.propositionSourceProducer
producerForSourceDiligenceGap sameObjectUnresolved = Search.identityProducer
producerForSourceDiligenceGap temporalScopeUnresolved = Search.temporalProducer
producerForSourceDiligenceGap coverageUnresolved = Search.empiricalEvidenceProducer
producerForSourceDiligenceGap contradictionSearchOpen = Search.contradictionProducer
producerForSourceDiligenceGap interpretationBoundaryOpen = Search.doctrinalComparisonProducer
producerForSourceDiligenceGap applicabilityOpen = Search.applicabilityProducer
producerForSourceDiligenceGap authorityOpen = Search.authorityDiscoveryProducer

record SourceDiligenceSearchDemand : Set where
  constructor source-diligence-search-demand
  field
    claimReference : String
    firstMissingSourceCoordinate : SourceDiligenceGap
    producer : Search.ProducerClass
    producerMatchesGap :
      producer ≡ producerForSourceDiligenceGap firstMissingSourceCoordinate
    consumerReference : String
    demandReference : String

open SourceDiligenceSearchDemand public

------------------------------------------------------------------------
-- Primary-source acquisition remains staged.  A located route is not a span,
-- and an inspected primary text is not yet proposition support.
------------------------------------------------------------------------

record PrimarySourceAcquisitionDemand : Set where
  constructor primary-source-acquisition-demand
  field
    claimReference : String
    target : Acquisition.SourceAcquisitionTarget
    acquisitionProducer : Search.ProducerClass
    acquisitionProducerIsPropositionSourceProducer :
      acquisitionProducer ≡ Search.propositionSourceProducer
    demandReference : String

open PrimarySourceAcquisitionDemand public

------------------------------------------------------------------------
-- A fully admitted SourceDiligence object is downstream of this search bridge.
-- Search output must not be confused with source admission or fact admission.
------------------------------------------------------------------------

data SearchResultIsSourceDiligence : Set where
data SourceDiligenceIsEmpiricalFactAdmission : Set where
data PrimarySourceLocatedMeansClaimSupported : Set where

searchResultDoesNotBecomeDiligenceByExistence : SearchResultIsSourceDiligence → ⊥
searchResultDoesNotBecomeDiligenceByExistence ()

sourceDiligenceDoesNotBecomeFactAdmissionByExistence :
  SourceDiligenceIsEmpiricalFactAdmission → ⊥
sourceDiligenceDoesNotBecomeFactAdmissionByExistence ()

primaryLocationDoesNotPayProposition :
  PrimarySourceLocatedMeansClaimSupported → ⊥
primaryLocationDoesNotPayProposition ()

record SourceDiligenceProofSearchBoundary : Set where
  constructor source-diligence-proof-search-boundary
  field
    sourceDiligenceUsesExistingProducerVocabulary : Bool
    sourceDiligenceUsesExistingProducerVocabularyIsTrue :
      sourceDiligenceUsesExistingProducerVocabulary ≡ true
    sourceAcquisitionAndPropositionSupportAreDistinct : Bool
    sourceAcquisitionAndPropositionSupportAreDistinctIsTrue :
      sourceAcquisitionAndPropositionSupportAreDistinct ≡ true
    searchHitEqualsSourceAdmission : Bool
    searchHitEqualsSourceAdmissionIsFalse : searchHitEqualsSourceAdmission ≡ false
    sourceAdmissionEqualsFactAdmission : Bool
    sourceAdmissionEqualsFactAdmissionIsFalse : sourceAdmissionEqualsFactAdmission ≡ false

canonicalSourceDiligenceProofSearchBoundary : SourceDiligenceProofSearchBoundary
canonicalSourceDiligenceProofSearchBoundary =
  source-diligence-proof-search-boundary true refl true refl false refl false refl
