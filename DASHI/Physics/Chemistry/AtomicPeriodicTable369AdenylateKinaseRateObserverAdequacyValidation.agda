module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseRateObserverAdequacyValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseRateObserverAdequacyExact as R

------------------------------------------------------------------------
-- RED/GREEN validation root: unweighted path topology is adequate for a
-- reachability query but not for an edge-rate query.  Adding the retained rate
-- coordinate repairs that information loss without pretending the individual
-- Figure 5/6 edge labels have already been acquired.
------------------------------------------------------------------------

topologyRegression :
  R.AdKRateObserverBoundary.topologyAdequateForReachability
    R.canonicalAdKRateObserverBoundary
  ≡ true
  × R.AdKRateObserverBoundary.topologyAdequateForTransitionRate
    R.canonicalAdKRateObserverBoundary
  ≡ false
topologyRegression = refl , refl

repairRegression :
  R.AdKRateObserverBoundary.enrichedObserverAdequateForTransitionRate
    R.canonicalAdKRateObserverBoundary
  ≡ true
  × R.AdKRateObserverBoundary.rateLabelsPresentInSourceFigures
    R.canonicalAdKRateObserverBoundary
  ≡ true
repairRegression = refl , refl

calibrationRegression :
  R.diffusionNumerator R.apoKramersCalibration ≡ 447
  × R.diffusionDenominator R.apoKramersCalibration ≡ 100000
  × R.diffusionNumerator R.boundKramersCalibration ≡ 513
  × R.diffusionDenominator R.boundKramersCalibration ≡ 1000000
calibrationRegression = refl , refl , refl , refl

acquisitionDebtRegression :
  R.AdKRateObserverBoundary.numericPerEdgeRateTableAcquired
    R.canonicalAdKRateObserverBoundary
  ≡ false
  × R.AdKRateObserverBoundary.kramersCalibrationEqualsExperimentalRateMeasurement
    R.canonicalAdKRateObserverBoundary
  ≡ false
acquisitionDebtRegression = refl , refl
