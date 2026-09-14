module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCouplingResidualValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCouplingResidualExact as C

------------------------------------------------------------------------
-- RED/GREEN validation root for the first source-paid dynamical coupling
-- residual over the NMP/LID fibre.  Reachability alone is insufficient: the
-- source must separately pay pathway order / relative flux information.
------------------------------------------------------------------------

pathwayOrderRegression :
  C.AdKCouplingBoundary.lidFirstPathwayObserved C.canonicalAdKCouplingBoundary ≡ true
  × C.AdKCouplingBoundary.nmpFirstPathwayObserved C.canonicalAdKCouplingBoundary ≡ true
pathwayOrderRegression = refl , refl

fluxRegression :
  C.primaryFluxNumerator C.canonicalCouplingResidual ≡ 57
  × C.primaryFluxDenominator C.canonicalCouplingResidual ≡ 10
  × C.AdKCouplingBoundary.relativePathwayFluxSourcePaid C.canonicalAdKCouplingBoundary ≡ true
fluxRegression = refl , refl , refl

nonPromotionRegression :
  C.AdKCouplingBoundary.offDiagonalReachabilityImpliesIndependence C.canonicalAdKCouplingBoundary ≡ false
  × C.AdKCouplingBoundary.fluxRatioIsUniversalRateConstant C.canonicalAdKCouplingBoundary ≡ false
  × C.AdKCouplingBoundary.computationalPathwayOrderIsExperimentalMechanism C.canonicalAdKCouplingBoundary ≡ false
nonPromotionRegression = refl , refl , refl
