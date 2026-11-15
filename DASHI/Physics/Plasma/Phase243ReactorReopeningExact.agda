module DASHI.Physics.Plasma.Phase243ReactorReopeningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.Phase243FreeBoundarySixExact as FB6
import DASHI.Physics.Plasma.Phase243ProducedFieldOrbitAtlasExact as Orbit
import DASHI.Physics.Plasma.Phase243SOTABenchmarkAtlasExact as SOTA

------------------------------------------------------------------------
-- DOWNSTREAM CONSUMER REOPENING
--
-- A quotient or Pareto choice is consumer-relative.  If a richer engineering,
-- transport, divertor, material or plant consumer distinguishes states that a
-- coarser ideal-plasma consumer identified, reopen only the residual coordinate
-- needed by that richer consumer.  Do not discard a lawful earlier quotient;
-- equally, do not let the earlier quotient erase downstream distinctions.
------------------------------------------------------------------------

data ReactorConsumer : Set where
  freeBoundaryEquilibriumConsumer : ReactorConsumer
  producedFieldOrbitConsumer : ReactorConsumer
  turbulenceTransportConsumer : ReactorConsumer
  bootstrapCurrentConsumer : ReactorConsumer
  mhdStabilityConsumer : ReactorConsumer
  divertorEdgeConsumer : ReactorConsumer
  coilForceClearanceConsumer : ReactorConsumer
  materialLifetimeConsumer : ReactorConsumer
  maintainabilityPortConsumer : ReactorConsumer
  netElectricPlantConsumer : ReactorConsumer

record ConsumerDistinguishes
    (consumer : ReactorConsumer)
    (left right : FB6.Candidate6) : Set₁ where
  constructor consumer-distinguishes
  field
    sameUpstreamEquivalenceClassReceipt : Set
    leftObservation rightObservation : Set
    distinctObservationReceipt : Set
    sameConsumerDefinitionReceipt : Set
    sameNormalizationReceipt : Set
    distinctionProvenance : String

open ConsumerDistinguishes public

record ReopenedResidual
    (consumer : ReactorConsumer)
    (left right : FB6.Candidate6) : Set₁ where
  constructor reopened-residual
  field
    witness : ConsumerDistinguishes consumer left right
    residualCoordinate : Set
    residualWasErasedUpstreamReceipt : Set
    residualRestoredForThisConsumerReceipt : Set
    upstreamValidResultsRemainValidReceipt : Set
    reopeningReference : String

open ReopenedResidual public

record ReactorReopeningBoundary : Set where
  constructor reactor-reopening-boundary
  field
    idealPlasmaQuotientIsUniversalEngineeringQuotient : Bool
    idealPlasmaQuotientIsUniversalEngineeringQuotientIsFalse :
      idealPlasmaQuotientIsUniversalEngineeringQuotient ≡ false
    richerConsumerMayReopenResidual : Bool
    richerConsumerMayReopenResidualIsTrue : richerConsumerMayReopenResidual ≡ true
    reopeningInvalidatesAllEarlierConsumers : Bool
    reopeningInvalidatesAllEarlierConsumersIsFalse :
      reopeningInvalidatesAllEarlierConsumers ≡ false
    paretoRankCanSuppressAConsumerDistinction : Bool
    paretoRankCanSuppressAConsumerDistinctionIsFalse :
      paretoRankCanSuppressAConsumerDistinction ≡ false
    sourceClaimCanSupplyMissingResidualCoordinateWithoutData : Bool
    sourceClaimCanSupplyMissingResidualCoordinateWithoutDataIsFalse :
      sourceClaimCanSupplyMissingResidualCoordinateWithoutData ≡ false

canonicalReactorReopeningBoundary : ReactorReopeningBoundary
canonicalReactorReopeningBoundary =
  reactor-reopening-boundary
    false refl
    true refl
    false refl
    false refl
    false refl

reopeningRule : String
reopeningRule =
  "Keep each quotient indexed by the consumer for which its sufficiency/equivariance was paid. When a richer downstream consumer separates quotient-equivalent states, reopen the least residual coordinate needed by that consumer, preserve earlier valid observations, and rerun only the downstream dependency cone."
