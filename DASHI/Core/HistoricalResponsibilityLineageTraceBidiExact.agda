module DASHI.Core.HistoricalResponsibilityLineageTraceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.HistoricalProducerResponsibilityTraceBidiExact as Responsibility
import DASHI.Core.TypedProvenancePathBidiExact as Path
import DASHI.Core.HistoricalFirstFailureTraceBidiExact as History
import DASHI.Core.QueryPromotionResidualBidiExact as QueryPromotion

------------------------------------------------------------------------
-- HISTORICAL PRODUCER RESPONSIBILITY <-> UPSTREAM LINEAGE
--
-- The producer who currently owes the first missing receipt is not thereby the
-- origin of the evidence/artifact lineage through which that obligation arose.
-- This owner keeps those two coordinates together without collapsing them.
------------------------------------------------------------------------

record HistoricalResponsibilityLineage
    (snapshot : History.HistoricalPromotionSnapshot) : Set₁ where
  constructor historical-responsibility-lineage
  field
    responsibility : Responsibility.HistoricalProducerResponsibility snapshot
    upstreamPath : Path.TypedProvenancePath
    obligationArrivalReference : String
    currentProducerReference : String
    lineageInterpretationReference : String

open HistoricalResponsibilityLineage public

currentProducerKind :
  ∀ {snapshot} →
  HistoricalResponsibilityLineage snapshot →
  QueryPromotion.ProducerKind
currentProducerKind trace =
  Responsibility.producerKind (responsibility trace)

upstreamDependenceReading :
  ∀ {snapshot} →
  (trace : HistoricalResponsibilityLineage snapshot) →
  Path.RootDependenceReading (upstreamPath trace)
upstreamDependenceReading trace =
  Path.canonicalRootDependenceReading (upstreamPath trace)

------------------------------------------------------------------------
-- Exact calibration: reuse the earlier missing-transport responsibility and a
-- typed reported lineage path.  The current work producer is `proveTransport`,
-- while the upstream lineage semantics remain `reportedBy` rather than being
-- rewritten as transport production.
------------------------------------------------------------------------

earlierTransportReportedLineage :
  HistoricalResponsibilityLineage History.earlierMissingTransport
earlierTransportReportedLineage =
  historical-responsibility-lineage
    Responsibility.earlierTransportResponsibility
    Path.reportedPath
    "historical promotion obligation arrived through a reported lineage path"
    "current first-missing-stage producer is proveTransport"
    "upstream report provenance and current transport-work responsibility are distinct coordinates"

earlierLineageCurrentProducerIsTransport :
  currentProducerKind earlierTransportReportedLineage ≡ QueryPromotion.proveTransport
earlierLineageCurrentProducerIsTransport = refl

earlierLineageSemanticsRemainReported :
  Path.edgeKinds (upstreamPath earlierTransportReportedLineage)
  ≡ (Path.Lineage.reportedBy ∷ [])
earlierLineageSemanticsRemainReported = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data CurrentProducerIsUpstreamOrigin : Set where
data HistoricalResponsibilityRewritesLineageSemantics : Set where
data UpstreamLineageCreatesCurrentProducerReceipt : Set where

currentProducerDoesNotBecomeUpstreamOrigin :
  CurrentProducerIsUpstreamOrigin → ⊥
currentProducerDoesNotBecomeUpstreamOrigin ()

responsibilityDoesNotRewriteLineageSemantics :
  HistoricalResponsibilityRewritesLineageSemantics → ⊥
responsibilityDoesNotRewriteLineageSemantics ()

upstreamLineageDoesNotCreateProducerReceipt :
  UpstreamLineageCreatesCurrentProducerReceipt → ⊥
upstreamLineageDoesNotCreateProducerReceipt ()

record HistoricalResponsibilityLineageBoundary : Set where
  constructor historical-responsibility-lineage-boundary
  field
    currentProducerAndUpstreamOriginAreDistinctCoordinates : Bool
    historicalResponsibilityRetainsTypedLineage : Bool
    responsibilityMayRewriteLineageSemantics : Bool
    upstreamPathCreatesMissingReceipt : Bool

canonicalHistoricalResponsibilityLineageBoundary :
  HistoricalResponsibilityLineageBoundary
canonicalHistoricalResponsibilityLineageBoundary =
  historical-responsibility-lineage-boundary true true false false
