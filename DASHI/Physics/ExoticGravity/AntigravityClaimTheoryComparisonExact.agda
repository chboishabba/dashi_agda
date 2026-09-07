module DASHI.Physics.ExoticGravity.AntigravityClaimTheoryComparisonExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Physics.ExoticGravity.AntigravityUnificationInteractionExact as Unified
import DASHI.Physics.GR.GravitationalObservationBidiExact as Obs
import DASHI.Physics.GR.GravitationalPredictionObservationBidiExact as Pred
import DASHI.Physics.GR.GravitationalPredictionAttributionBidiExact as Attr
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- CLAIM-INDEXED ATTRIBUTED THEORY COMPARISON
--
-- ObservationTheoryComparison already binds observation and attributed
-- predictions.  This wrapper adds the missing originating antigravity consumer:
-- the exact claim, its exact gravitational route and one shared comparison claim
-- scope consumed by both predictions and the experimental result analysis.
------------------------------------------------------------------------

record AntigravityMeasurementClaimBinding
    (claim : Anti.AntigravityClaim) : Set where
  constructor antigravity-measurement-claim-binding
  field
    route : Unified.GravitationalClaimRoute claim
    observation : Obs.GravitationalObservationReceipt
    observationChannelMatchesRoute :
      Obs.channel observation ≡ Unified.GravitationalClaimRoute.channel route
    comparisonClaimScope : String
    resultClaimScope : String
    resultClaimScopeMatches : resultClaimScope ≡ comparisonClaimScope
    claimBindingCarrier : String

open AntigravityMeasurementClaimBinding public

record ClaimIndexedTheoryComparison
    (claim : Anti.AntigravityClaim) : Set where
  constructor claim-indexed-theory-comparison
  field
    measurementBinding : AntigravityMeasurementClaimBinding claim
    comparison : Unified.ObservationTheoryComparison

    comparisonObservationMatches :
      Unified.observation comparison ≡ observation measurementBinding

    ordinaryPredictionScopeMatches :
      Pred.predictionClaimScope
        (Attr.prediction (Unified.ordinaryGRPrediction comparison))
        ≡ comparisonClaimScope measurementBinding

    modifiedPredictionScopeMatches :
      Pred.predictionClaimScope
        (Attr.prediction (Unified.modifiedGravityPrediction comparison))
        ≡ comparisonClaimScope measurementBinding

    ordinaryPredictionIsGR :
      Pred.theoryFamily
        (Attr.prediction (Unified.ordinaryGRPrediction comparison))
        ≡ Pred.generalRelativityTheory

open ClaimIndexedTheoryComparison public

------------------------------------------------------------------------
-- Reverse-search residuals for the comparison handoff.
------------------------------------------------------------------------

data ClaimComparisonResidual : Set where
  missingClaimBoundMeasurement : ClaimComparisonResidual
  missingOrdinaryAttributedPrediction : ClaimComparisonResidual
  missingAlternativeAttributedPrediction : ClaimComparisonResidual
  missingOrdinaryPredictionWeld : ClaimComparisonResidual
  missingAlternativePredictionWeld : ClaimComparisonResidual
  missingExactSharedClaimScope : ClaimComparisonResidual
  missingPairedComparisonLineage : ClaimComparisonResidual
  comparisonResidualOpen : ClaimComparisonResidual

producerForClaimComparisonResidual :
  ClaimComparisonResidual → Search.ProducerClass
producerForClaimComparisonResidual missingClaimBoundMeasurement =
  Search.empiricalEvidenceProducer
producerForClaimComparisonResidual missingOrdinaryAttributedPrediction =
  Search.propositionSourceProducer
producerForClaimComparisonResidual missingAlternativeAttributedPrediction =
  Search.propositionSourceProducer
producerForClaimComparisonResidual missingOrdinaryPredictionWeld =
  Search.identityProducer
producerForClaimComparisonResidual missingAlternativePredictionWeld =
  Search.identityProducer
producerForClaimComparisonResidual missingExactSharedClaimScope =
  Search.discriminatorProducer
producerForClaimComparisonResidual missingPairedComparisonLineage =
  Search.attributionProducer
producerForClaimComparisonResidual comparisonResidualOpen =
  Search.contradictionProducer

------------------------------------------------------------------------
-- Introspective collision: same observation channel does not by itself identify
-- the consumer claim.  This finite fixture keeps the channel fixed while the
-- downstream claim differs.
------------------------------------------------------------------------

data SameChannelClaimFixture : Set where
  freeFallClaimFixture passiveWeightClaimFixture : SameChannelClaimFixture

data CoarseChannelLabel : Set where
  laboratoryGravityChannel : CoarseChannelLabel

data ClaimDecision : Set where
  freeFallConsumerDecision passiveWeightConsumerDecision : ClaimDecision

coarseChannelObserver : SameChannelClaimFixture → CoarseChannelLabel
coarseChannelObserver _ = laboratoryGravityChannel

fixtureClaimDecision : SameChannelClaimFixture → ClaimDecision
fixtureClaimDecision freeFallClaimFixture = freeFallConsumerDecision
fixtureClaimDecision passiveWeightClaimFixture = passiveWeightConsumerDecision

sameChannelCollision :
  coarseChannelObserver freeFallClaimFixture
    ≡ coarseChannelObserver passiveWeightClaimFixture
sameChannelCollision = refl

channelAloneDoesNotFixClaimDecision :
  fixtureClaimDecision freeFallClaimFixture
    ≡ fixtureClaimDecision passiveWeightClaimFixture → ⊥
channelAloneDoesNotFixClaimDecision ()

record ClaimTheoryComparisonBoundary : Set where
  constructor claim-theory-comparison-boundary
  field
    observationChannelAloneFixesConsumerClaim : Bool
    exactOriginatingClaimRequired : Bool
    exactSharedPredictionClaimScopeRequired : Bool
    ordinaryPredictionMustBeGR : Bool
    attributedPredictionsAutomaticallyMatchMeasurement : Bool
    betterAlternativeFitAutomaticallyProvesAlternativeTheory : Bool
    completedComparisonAutomaticallyProvesAntigravity : Bool
    comparisonResidualMayReopenTheorySearch : Bool

canonicalClaimTheoryComparisonBoundary : ClaimTheoryComparisonBoundary
canonicalClaimTheoryComparisonBoundary =
  claim-theory-comparison-boundary
    false true true true false false false true
