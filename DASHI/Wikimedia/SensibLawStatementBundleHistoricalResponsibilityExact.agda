module DASHI.Wikimedia.SensibLawStatementBundleHistoricalResponsibilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.HistoricalProducerResponsibilityTraceBidiExact as GenericResponsibility
import DASHI.Core.HistoricalResponsibilityLineageTraceBidiExact as GenericLineage
import DASHI.Core.HistoricalFirstFailureTraceBidiExact as GenericHistory
import DASHI.Core.TemporalPromotionNonRetroactivityBidiExact as Temporal
import DASHI.Wikimedia.SensibLawStatementBundlePrerequisiteDAGExact as DAG

------------------------------------------------------------------------
-- BUNDLE PREREQUISITE FIRST FAILURE -> HISTORICAL WORK RESPONSIBILITY
--
-- This is a domain refinement of the generic historical-responsibility law.
-- The generic owner works over promotion stages; this owner retains the finer
-- Wikidata statement-bundle prerequisite cut.  Responsibility means who/what
-- producer must pay the current work obligation, never blame, liability or
-- authority.
------------------------------------------------------------------------

record BundleHistoricalResponsibility
    (snapshot : DAG.TimedPrerequisiteSnapshot) : Set where
  constructor bundle-historical-responsibility
  field
    firstResidual : DAG.BundlePrerequisiteResidual
    firstResidualExact :
      firstResidual ≡ DAG.firstResidual (DAG.cut snapshot)
    requiredProducer : DAG.BundlePrerequisiteProducer
    requiredProducerExact :
      requiredProducer ≡ DAG.producerForResidual firstResidual
    mechanism : DAG.PrerequisiteMechanism
    mechanismExact :
      mechanism ≡ DAG.mechanismForProducer requiredProducer
    responsibilityReference : String
    upstreamLineageReference : String
open BundleHistoricalResponsibility public

responsibilityFor :
  (snapshot : DAG.TimedPrerequisiteSnapshot) →
  BundleHistoricalResponsibility snapshot
responsibilityFor snapshot =
  bundle-historical-responsibility
    (DAG.firstResidual (DAG.cut snapshot))
    refl
    (DAG.producerForResidual (DAG.firstResidual (DAG.cut snapshot)))
    refl
    (DAG.mechanismForProducer
      (DAG.producerForResidual (DAG.firstResidual (DAG.cut snapshot))))
    refl
    "first unpaid bundle prerequisite selects current proof/work responsibility"
    "upstream source/transport lineage remains separately typed and does not become the producer receipt"

earlierNatResponsibility :
  BundleHistoricalResponsibility DAG.earlierNatSnapshot
earlierNatResponsibility = responsibilityFor DAG.earlierNatSnapshot

laterNatResponsibility :
  BundleHistoricalResponsibility DAG.laterNatSnapshot
laterNatResponsibility = responsibilityFor DAG.laterNatSnapshot

earlierNatResponsibilityIsSourceSupport :
  firstResidual earlierNatResponsibility ≡ DAG.missingSourceSupport
earlierNatResponsibilityIsSourceSupport = refl

earlierNatProducerIsAcquireSourceSupport :
  requiredProducer earlierNatResponsibility ≡ DAG.acquireSourceSupport
earlierNatProducerIsAcquireSourceSupport = refl

laterNatResponsibilityIsQualifierTransport :
  firstResidual laterNatResponsibility ≡ DAG.missingQualifierTransport
laterNatResponsibilityIsQualifierTransport = refl

laterNatProducerIsQualifierProof :
  requiredProducer laterNatResponsibility ≡ DAG.proveQualifierTransport
laterNatProducerIsQualifierProof = refl

------------------------------------------------------------------------
-- The generic historical machinery remains authoritative for the shared laws.
-- We consume its boundaries instead of restating them as new principles.
------------------------------------------------------------------------

genericResponsibilityIsTimeIndexed : Bool
genericResponsibilityIsTimeIndexed =
  GenericResponsibility.responsibilityIsTimeIndexed
    GenericResponsibility.canonicalHistoricalProducerResponsibilityBoundary

genericLaterClosureDoesNotRewriteEarlierResponsibility : Bool
genericLaterClosureDoesNotRewriteEarlierResponsibility =
  GenericResponsibility.laterClosureRewritesEarlierResponsibility
    GenericResponsibility.canonicalHistoricalProducerResponsibilityBoundary

genericCurrentProducerAndOriginStayDistinct : Bool
genericCurrentProducerAndOriginStayDistinct =
  GenericLineage.currentProducerAndUpstreamOriginAreDistinctCoordinates
    GenericLineage.canonicalHistoricalResponsibilityLineageBoundary

genericHistoricalFirstFailureIsTimeIndexed : Bool
genericHistoricalFirstFailureIsTimeIndexed =
  GenericHistory.firstFailureIsTimeIndexed
    GenericHistory.canonicalHistoricalFirstFailureBoundary

bundleEarlierAndLaterUseDifferentCurrentProducers :
  requiredProducer earlierNatResponsibility ≡ requiredProducer laterNatResponsibility → ⊥
bundleEarlierAndLaterUseDifferentCurrentProducers ()

------------------------------------------------------------------------
-- No-collapse boundaries.
------------------------------------------------------------------------

data BundleResponsibilityMeansBlame : Set where
data CurrentProducerBecomesUpstreamOrigin : Set where
data LaterPaymentBackdatesEarlierPossession : Set where
data UpstreamLineagePaysCurrentPrerequisite : Set where

bundleResponsibilityDoesNotMeanBlame : BundleResponsibilityMeansBlame → ⊥
bundleResponsibilityDoesNotMeanBlame ()

currentProducerDoesNotBecomeUpstreamOrigin : CurrentProducerBecomesUpstreamOrigin → ⊥
currentProducerDoesNotBecomeUpstreamOrigin ()

laterPaymentDoesNotBackdateEarlierPossession :
  LaterPaymentBackdatesEarlierPossession → ⊥
laterPaymentDoesNotBackdateEarlierPossession ()

upstreamLineageDoesNotPayCurrentPrerequisite :
  UpstreamLineagePaysCurrentPrerequisite → ⊥
upstreamLineageDoesNotPayCurrentPrerequisite ()

record BundleHistoricalResponsibilityBoundary : Set where
  constructor bundle-historical-responsibility-boundary
  field
    firstMissingSelectsCurrentWorkProducer : Bool
    responsibilityTimeIndexed : Bool
    laterPaymentRewritesEarlierFailure : Bool
    producerResponsibilityMeansBlame : Bool
    currentProducerIsUpstreamOrigin : Bool
    upstreamLineageCreatesReceipt : Bool

canonicalBundleHistoricalResponsibilityBoundary :
  BundleHistoricalResponsibilityBoundary
canonicalBundleHistoricalResponsibilityBoundary =
  bundle-historical-responsibility-boundary true true false false false false
