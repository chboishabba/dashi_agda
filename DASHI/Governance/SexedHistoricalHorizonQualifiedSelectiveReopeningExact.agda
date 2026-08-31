module DASHI.Governance.SexedHistoricalHorizonQualifiedSelectiveReopeningExact where

------------------------------------------------------------------------
-- HORIZON-QUALIFIED SELECTIVE REOPENING
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
-- 3. Homogeneous artifact carrier for canonical dependency closure.
------------------------------------------------------------------------

data HorizonArtifact : Set where
  divergenceArtifact : ForecastDivergenceEvent → HorizonArtifact
  certificateArtifact : ForecastCertificate → HorizonArtifact

data Depends : HorizonArtifact → HorizonArtifact → Set where
  divergenceToLongForecast :
    Depends
      (divergenceArtifact firstLongDivergence)
      (certificateArtifact longForecastCertificate)
  longForecastToPlanning :
    Depends
      (certificateArtifact longForecastCertificate)
      (certificateArtifact longPlanningCertificate)
  planningToCollectiveFuture :
    Depends
      (certificateArtifact longPlanningCertificate)
      (certificateArtifact longCollectiveFutureCertificate)

------------------------------------------------------------------------
-- 4. Canonical reopening obligations at/above first divergence horizon.
------------------------------------------------------------------------

longForecastMustReopen :
  Dependency.ReopeningObligation
    Depends
    (divergenceArtifact firstLongDivergence)
    (certificateArtifact longForecastCertificate)
longForecastMustReopen =
  Dependency.oneEdgeCreatesReopeningObligation divergenceToLongForecast

longPlanningMustReopen :
  Dependency.ReopeningObligation
    Depends
    (divergenceArtifact firstLongDivergence)
    (certificateArtifact longPlanningCertificate)
longPlanningMustReopen =
  Dependency.obligationsCompose
    (Dependency.oneEdgeCreatesReopeningObligation divergenceToLongForecast)
    (Dependency.oneEdgeCreatesReopeningObligation longForecastToPlanning)

longCollectiveFutureMustReopen :
  Dependency.ReopeningObligation
    Depends
    (divergenceArtifact firstLongDivergence)
    (certificateArtifact longCollectiveFutureCertificate)
longCollectiveFutureMustReopen =
  Dependency.obligationsCompose
    longPlanningMustReopen
    (Dependency.oneEdgeCreatesReopeningObligation planningToCollectiveFuture)

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
