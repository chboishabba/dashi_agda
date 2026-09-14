module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETThirdAxisValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETThirdAxisExact as T

------------------------------------------------------------------------
-- RED/GREEN validation root: a two-axis observer join is still query-relative.
------------------------------------------------------------------------

twoAxisBoundaryRegression :
  T.AdKFRETThirdAxisBoundary.twoFretAxisJoinRetainsDeclaredTwoAxes
    T.canonicalAdKFRETThirdAxisBoundary
  ≡ true
  × T.AdKFRETThirdAxisBoundary.twoFretAxisJoinAdequateForThirdCoordinate
    T.canonicalAdKFRETThirdAxisBoundary
  ≡ false
twoAxisBoundaryRegression = refl , refl

repairRegression :
  T.AdKFRETThirdAxisBoundary.threeAxisObserverAdequateForThirdCoordinate
    T.canonicalAdKFRETThirdAxisBoundary
  ≡ true
  × T.AdKFRETThirdAxisBoundary.sourcePaysThreeCvStateDescription
    T.canonicalAdKFRETThirdAxisBoundary
  ≡ true
repairRegression = refl , refl

promotionRegression :
  T.AdKFRETThirdAxisBoundary.finiteThirdAxisCollisionIsHistoricalSameMoleculeMeasurement
    T.canonicalAdKFRETThirdAxisBoundary
  ≡ false
  × T.AdKFRETThirdAxisBoundary.threeCoordinatesEqualCompleteProteinState
    T.canonicalAdKFRETThirdAxisBoundary
  ≡ false
promotionRegression = refl , refl
