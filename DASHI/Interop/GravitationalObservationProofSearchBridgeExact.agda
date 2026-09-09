module DASHI.Interop.GravitationalObservationProofSearchBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.GR.GravitationalObservationBidiExact as Obs
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- GRAVITATIONAL OBSERVATION RESIDUAL -> EXISTING PRODUCER CLASS
--
-- Reuse the existing proof-directed search vocabulary.  The bridge does not
-- create a physics-specific retrieval engine and retrieval still does not pay
-- the evidentiary or physical claim by existence.
------------------------------------------------------------------------

producerForObservationResidual : Obs.ObservationResidual → Search.ProducerClass
producerForObservationResidual Obs.missingAttributedCarrier = Search.attributionProducer
producerForObservationResidual Obs.missingCalibration = Search.empiricalEvidenceProducer
producerForObservationResidual Obs.missingNoiseCharacterisation = Search.empiricalEvidenceProducer
producerForObservationResidual Obs.missingCoincidenceOrCorrelation = Search.discriminatorProducer
producerForObservationResidual Obs.missingWaveformOrSourceModel = Search.propositionSourceProducer
producerForObservationResidual Obs.missingDistanceOrSkyConsistency = Search.empiricalEvidenceProducer
producerForObservationResidual Obs.missingGRComparator = Search.propositionSourceProducer
producerForObservationResidual Obs.missingAlternativeGravityComparator = Search.contradictionProducer
producerForObservationResidual Obs.missingExactDataRevision = Search.attributionProducer

record GravitationalObservationSearchBoundary : Set where
  constructor gravitational-observation-search-boundary
  field
    missingCarrierRoutesToAttribution : Bool
    calibrationAndNoiseRouteToEmpiricalEvidence : Bool
    coincidenceRoutesToDiscriminator : Bool
    alternativeComparatorRoutesToContradictionSearch : Bool
    searchHitAutomaticallyPaysObservationResidual : Bool
    searchResultAutomaticallyPromotesModifiedGravity : Bool

canonicalGravitationalObservationSearchBoundary : GravitationalObservationSearchBoundary
canonicalGravitationalObservationSearchBoundary =
  gravitational-observation-search-boundary true true true true false false

attributionRouteExact :
  producerForObservationResidual Obs.missingAttributedCarrier
    ≡ Search.attributionProducer
attributionRouteExact = refl

calibrationRouteExact :
  producerForObservationResidual Obs.missingCalibration
    ≡ Search.empiricalEvidenceProducer
calibrationRouteExact = refl

alternativeComparatorRouteExact :
  producerForObservationResidual Obs.missingAlternativeGravityComparator
    ≡ Search.contradictionProducer
alternativeComparatorRouteExact = refl
