module DASHI.Governance.SexedHistoricalHorizonQualifiedSelectiveReopeningExact where

------------------------------------------------------------------------
-- HORIZON-QUALIFIED SELECTIVE REOPENING
--
-- If two live histories first diverge only at horizon k, certificates scoped
-- strictly below k remain retained.  Certificates whose declared forecast
-- horizon reaches k reopen through an explicit dependency graph.
--
-- First forecast divergence is an observation-depth fact, not a historical
-- change point.  Retention below k is scoped to this finite fixture and does
-- not imply permanent closure under arbitrary future evidence.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Governance.SexedHistoricalHorizonFiltrationFirstDivergenceExact as Horizon

------------------------------------------------------------------------
-- 1. Forecast certificates carry declared horizon scope.
------------------------------------------------------------------------

data ForecastCertificate : Set where
  immediateActionCertificate
  shortForecastCertificate
  mediumForecastCertificate
  longForecastCertificate
  longPlanningCertificate
  longCollectiveFutureCertificate
  : ForecastCertificate

certificateHorizon : ForecastCertificate → Horizon.Horizon
certificateHorizon immediateActionCertificate = Horizon.shortHorizon
certificateHorizon shortForecastCertificate = Horizon.shortHorizon
certificateHorizon mediumForecastCertificate = Horizon.mediumHorizon
certificateHorizon longForecastCertificate = Horizon.longHorizon
certificateHorizon longPlanningCertificate = Horizon.longHorizon
certificateHorizon longCollectiveFutureCertificate = Horizon.longHorizon

------------------------------------------------------------------------
-- 2. First-divergence event and horizon reachability.
------------------------------------------------------------------------

data ForecastDivergenceEvent : Set where
  firstLongDivergence : ForecastDivergenceEvent

firstDivergenceHorizon : ForecastDivergenceEvent → Horizon.Horizon
firstDivergenceHorizon firstLongDivergence = Horizon.longHorizon

record ReachesDivergenceHorizon
    (event : ForecastDivergenceEvent)
    (certificate : ForecastCertificate) : Set where
  constructor reaches-divergence-horizon
  field
    horizonWitness :
      Horizon.HorizonLe
        (firstDivergenceHorizon event)
        (certificateHorizon certificate)

longForecastReachesFirstDivergence :
  ReachesDivergenceHorizon firstLongDivergence longForecastCertificate
longForecastReachesFirstDivergence =
  reaches-divergence-horizon Horizon.longRefl

longPlanningReachesFirstDivergence :
  ReachesDivergenceHorizon firstLongDivergence longPlanningCertificate
longPlanningReachesFirstDivergence =
  reaches-divergence-horizon Horizon.longRefl

shortDoesNotReachLongDivergence :
  ReachesDivergenceHorizon firstLongDivergence shortForecastCertificate → ⊥
shortDoesNotReachLongDivergence (reaches-divergence-horizon ())

mediumDoesNotReachLongDivergence :
  ReachesDivergenceHorizon firstLongDivergence mediumForecastCertificate → ⊥
mediumDoesNotReachLongDivergence (reaches-divergence-horizon ())

------------------------------------------------------------------------
-- 3. Dependency graph: first divergence affects only horizon-qualified lanes.
------------------------------------------------------------------------

data Depends : Set where
  divergenceToLongForecast :
    Depends firstLongDivergence longForecastCertificate
  longForecastToPlanning :
    Depends longForecastCertificate longPlanningCertificate
  planningToCollectiveFuture :
    Depends longPlanningCertificate longCollectiveFutureCertificate

------------------------------------------------------------------------
-- 4. Canonical reopening obligations at/above the first divergence horizon.
------------------------------------------------------------------------

longForecastMustReopen :
  Dependency.ReopeningObligation
    Depends firstLongDivergence longForecastCertificate
longForecastMustReopen =
  Dependency.directReopening divergenceToLongForecast

longPlanningMustReopen :
  Dependency.ReopeningObligation
    Depends firstLongDivergence longPlanningCertificate
longPlanningMustReopen =
  Dependency.obligationsCompose
    (Dependency.directReopening divergenceToLongForecast)
    (Dependency.directReopening longForecastToPlanning)

longCollectiveFutureMustReopen :
  Dependency.ReopeningObligation
    Depends firstLongDivergence longCollectiveFutureCertificate
longCollectiveFutureMustReopen =
  Dependency.obligationsCompose
    longPlanningMustReopen
    (Dependency.directReopening planningToCollectiveFuture)

------------------------------------------------------------------------
-- 5. Explicit retention below the first-divergence horizon.
------------------------------------------------------------------------

data RetainedBelowFirstDivergence : ForecastCertificate → Set where
  immediateRetained : RetainedBelowFirstDivergence immediateActionCertificate
  shortRetained : RetainedBelowFirstDivergence shortForecastCertificate
  mediumRetained : RetainedBelowFirstDivergence mediumForecastCertificate

canonicalImmediateRetention :
  RetainedBelowFirstDivergence immediateActionCertificate
canonicalImmediateRetention = immediateRetained

canonicalShortRetention :
  RetainedBelowFirstDivergence shortForecastCertificate
canonicalShortRetention = shortRetained

canonicalMediumRetention :
  RetainedBelowFirstDivergence mediumForecastCertificate
canonicalMediumRetention = mediumRetained

longForecastIsNotRetainedBelowDivergence :
  RetainedBelowFirstDivergence longForecastCertificate → ⊥
longForecastIsNotRetainedBelowDivergence ()

------------------------------------------------------------------------
-- 6. Horizon disposition and reopening policy align.
------------------------------------------------------------------------

data ReopeningDisposition : Set where
  retainCertificate reopenCertificate : ReopeningDisposition

reopeningDisposition : ForecastCertificate → ReopeningDisposition
reopeningDisposition immediateActionCertificate = retainCertificate
reopeningDisposition shortForecastCertificate = retainCertificate
reopeningDisposition mediumForecastCertificate = retainCertificate
reopeningDisposition longForecastCertificate = reopenCertificate
reopeningDisposition longPlanningCertificate = reopenCertificate
reopeningDisposition longCollectiveFutureCertificate = reopenCertificate

shortDispositionRetained :
  reopeningDisposition shortForecastCertificate ≡ retainCertificate
shortDispositionRetained = refl

mediumDispositionRetained :
  reopeningDisposition mediumForecastCertificate ≡ retainCertificate
mediumDispositionRetained = refl

longDispositionReopens :
  reopeningDisposition longForecastCertificate ≡ reopenCertificate
longDispositionReopens = refl

------------------------------------------------------------------------
-- 7. No-promotion boundaries.
------------------------------------------------------------------------

data LongDivergenceInvalidatesShortAction : Set where

data FirstDivergenceReopensEveryCertificate : Set where

data RetainedBelowDivergenceMeansPermanentlyClosed : Set where

data ForecastHorizonIsHistoricalTime : Set where

data LongForecastReopeningMeansEarlierForecastWasFalse : Set where

data HorizonScopeDeterminesSemanticImportance : Set where

longDivergenceDoesNotInvalidateShortAction :
  LongDivergenceInvalidatesShortAction → ⊥
longDivergenceDoesNotInvalidateShortAction ()

firstDivergenceDoesNotReopenEveryCertificate :
  FirstDivergenceReopensEveryCertificate → ⊥
firstDivergenceDoesNotReopenEveryCertificate ()

retentionDoesNotMeanPermanentClosure :
  RetainedBelowDivergenceMeansPermanentlyClosed → ⊥
retentionDoesNotMeanPermanentClosure ()

forecastHorizonIsNotHistoricalTime : ForecastHorizonIsHistoricalTime → ⊥
forecastHorizonIsNotHistoricalTime ()

reopeningDoesNotMeanEarlierForecastWasFalse :
  LongForecastReopeningMeansEarlierForecastWasFalse → ⊥
reopeningDoesNotMeanEarlierForecastWasFalse ()

horizonScopeDoesNotDetermineSemanticImportance :
  HorizonScopeDeterminesSemanticImportance → ⊥
horizonScopeDoesNotDetermineSemanticImportance ()

record HorizonQualifiedSelectiveReopeningBoundary : Set where
  constructor horizon-qualified-selective-reopening-boundary
  field
    firstLongDivergenceOwned : Bool
    shortCertificateRetained : Bool
    mediumCertificateRetained : Bool
    longForecastReopened : Bool
    longPlanningReopenedTransitively : Bool
    collectiveFutureReopenedTransitively : Bool
    firstDivergenceReopensEverything : Bool
    retentionMeansPermanentClosure : Bool
    forecastHorizonEqualsHistoricalTime : Bool

canonicalHorizonQualifiedSelectiveReopeningBoundary :
  HorizonQualifiedSelectiveReopeningBoundary
canonicalHorizonQualifiedSelectiveReopeningBoundary =
  horizon-qualified-selective-reopening-boundary
    true true true true true true false false false
