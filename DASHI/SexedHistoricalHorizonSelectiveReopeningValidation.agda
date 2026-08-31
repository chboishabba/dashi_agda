module DASHI.SexedHistoricalHorizonSelectiveReopeningValidation where

open import DASHI.Core.Prelude

import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Governance.SexedHistoricalHorizonFiltrationFirstDivergenceExact as Horizon
import DASHI.Governance.SexedHistoricalHorizonQualifiedSelectiveReopeningExact as Reopen

firstDivergenceStillLongRegression :
  Horizon.FirstForecastDivergenceAt Horizon.longHorizon
firstDivergenceStillLongRegression =
  Horizon.canonicalFirstForecastDivergence

shortRetentionRegression :
  Reopen.RetainedBelowFirstDivergence Reopen.shortForecastCertificate
shortRetentionRegression = Reopen.canonicalShortRetention

mediumRetentionRegression :
  Reopen.RetainedBelowFirstDivergence Reopen.mediumForecastCertificate
mediumRetentionRegression = Reopen.canonicalMediumRetention

longForecastReopeningRegression :
  Dependency.ReopeningObligation
    Reopen.Depends
    (Reopen.divergenceArtifact Reopen.firstLongDivergence)
    (Reopen.certificateArtifact Reopen.longForecastCertificate)
longForecastReopeningRegression = Reopen.longForecastMustReopen

longPlanningReopeningRegression :
  Dependency.ReopeningObligation
    Reopen.Depends
    (Reopen.divergenceArtifact Reopen.firstLongDivergence)
    (Reopen.certificateArtifact Reopen.longPlanningCertificate)
longPlanningReopeningRegression = Reopen.longPlanningMustReopen

collectiveFutureReopeningRegression :
  Dependency.ReopeningObligation
    Reopen.Depends
    (Reopen.divergenceArtifact Reopen.firstLongDivergence)
    (Reopen.certificateArtifact Reopen.longCollectiveFutureCertificate)
collectiveFutureReopeningRegression = Reopen.longCollectiveFutureMustReopen

shortDoesNotReachLongRegression :
  Reopen.ReachesDivergenceHorizon
    Reopen.firstLongDivergence Reopen.shortForecastCertificate → ⊥
shortDoesNotReachLongRegression = Reopen.shortDoesNotReachLongDivergence

mediumDoesNotReachLongRegression :
  Reopen.ReachesDivergenceHorizon
    Reopen.firstLongDivergence Reopen.mediumForecastCertificate → ⊥
mediumDoesNotReachLongRegression = Reopen.mediumDoesNotReachLongDivergence

longDispositionRegression :
  Reopen.reopeningDisposition Reopen.longForecastCertificate
  ≡ Reopen.reopenCertificate
longDispositionRegression = Reopen.longDispositionReopens

boundaryRegression : Reopen.HorizonQualifiedSelectiveReopeningBoundary
boundaryRegression = Reopen.canonicalHorizonQualifiedSelectiveReopeningBoundary
