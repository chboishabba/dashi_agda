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
-- predictions.  This wrapper retains the originating antigravity consumer:
-- the exact claim, its exact gravitational route and one shared comparison claim
-- scope consumed by both predictions and the experimental result analysis.
-- Current typed gravitational routes distinguish the currently enumerated
-- gravitational claims; the explicit claim index is retained for scope,
-- provenance and future-refinement stability rather than to repair a present
-- typed-channel collision.
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
-- Introspective collision at the deliberately coarse observation-family level.
-- The current exact typed routes are distinct; the coarse label below erases
-- that distinction and therefore cannot determine the downstream consumer.
------------------------------------------------------------------------

data CoarseLaboratoryClaimFixture : Set where
  freeFallClaimFixture passiveWeightClaimFixture : CoarseLaboratoryClaimFixture

data CoarseObservationFamily : Set where
  laboratoryGravityObservation : CoarseObservationFamily

data ClaimDecision : Set where
  freeFallConsumerDecision passiveWeightConsumerDecision : ClaimDecision

coarseObservationFamily : CoarseLaboratoryClaimFixture → CoarseObservationFamily
coarseObservationFamily _ = laboratoryGravityObservation

fixtureClaimDecision : CoarseLaboratoryClaimFixture → ClaimDecision
fixtureClaimDecision freeFallClaimFixture = freeFallConsumerDecision
fixtureClaimDecision passiveWeightClaimFixture = passiveWeightConsumerDecision

coarseObservationFamilyCollision :
  coarseObservationFamily freeFallClaimFixture
    ≡ coarseObservationFamily passiveWeightClaimFixture
coarseObservationFamilyCollision = refl

coarseFamilyDoesNotFixClaimDecision :
  fixtureClaimDecision freeFallClaimFixture
    ≡ fixtureClaimDecision passiveWeightClaimFixture → ⊥
coarseFamilyDoesNotFixClaimDecision ()

record ClaimTheoryComparisonBoundary : Set where
  constructor claim-theory-comparison-boundary
  field
    coarseLaboratoryGravityLabelFixesConsumerClaim : Bool
    currentTypedGravityRoutesSeparateEnumeratedGravityClaims : Bool
    exactOriginatingClaimRetainedForScopeAndProvenance : Bool
    exactSharedPredictionClaimScopeRequired : Bool
    ordinaryPredictionMustBeGR : Bool
    attributedPredictionsAutomaticallyMatchMeasurement : Bool
    betterAlternativeFitAutomaticallyProvesAlternativeTheory : Bool
    completedComparisonAutomaticallyProvesAntigravity : Bool
    comparisonResidualMayReopenTheorySearch : Bool

canonicalClaimTheoryComparisonBoundary : ClaimTheoryComparisonBoundary
canonicalClaimTheoryComparisonBoundary =
  claim-theory-comparison-boundary
    false true true true true false false false true
