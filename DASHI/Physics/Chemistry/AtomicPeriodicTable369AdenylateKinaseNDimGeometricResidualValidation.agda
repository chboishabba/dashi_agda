module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseNDimGeometricResidualValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseNDimGeometricResidualExact as N

------------------------------------------------------------------------
-- RED/GREEN validation root: replace the binary open/closed label by a
-- source-paid multidimensional geometric residual over the same 4AKE/1AKE pair.
------------------------------------------------------------------------

coordinateRegression :
  N.nmpCoreTenthsAngstrom N.openGeometricResidual ≡ 627
  × N.lidCoreTenthsAngstrom N.openGeometricResidual ≡ 701
  × N.nmpCoreTenthsAngstrom N.closedGeometricResidual ≡ 184
  × N.lidCoreTenthsAngstrom N.closedGeometricResidual ≡ 210
coordinateRegression = refl , refl , refl , refl

separationRegression :
  N.AdKNDimGeometricBoundary.bothMeasuredAxesSeparateEndpoints
    N.canonicalAdKNDimGeometricBoundary
  ≡ true
  × N.AdKNDimGeometricBoundary.sequenceAloneDeterminesGeometricResidual
    N.canonicalAdKNDimGeometricBoundary
  ≡ false
separationRegression = refl , refl

ndimDisciplineRegression :
  N.AdKNDimGeometricBoundary.moreCoordinatesAutomaticallyImproveConsumer
    N.canonicalAdKNDimGeometricBoundary
  ≡ false
  × N.AdKNDimGeometricBoundary.fullSE3InvariantTheoremPaid
    N.canonicalAdKNDimGeometricBoundary
  ≡ false
ndimDisciplineRegression = refl , refl
