module DASHI.Analysis.RiemannG2DirectInputsToAnalyticCoresRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Analysis.RiemannG2DirectInputsToAnalyticCoresExact as Direct

private
  boundary = Direct.canonicalDirectInputsToAnalyticCoresBoundary

historicalRouteNotIndependent :
  Direct.historicalDirectRouteIsIndependentTerminalAPI boundary ≡ false
historicalRouteNotIndependent = refl

offFactorsDefinitionally :
  Direct.directOffPaymentDefinitionallyFactorsThroughCore boundary ≡ true
offFactorsDefinitionally = refl

gammaFactorsDefinitionally :
  Direct.directGammaPaymentDefinitionallyFactorsThroughCore boundary ≡ true
gammaFactorsDefinitionally = refl

certifiedUpperCompilesCore :
  Direct.certifiedFiniteUpperRouteCompilesOffAnalyticCore boundary ≡ true
certifiedUpperCompilesCore = refl

representationNotAnalysis :
  Direct.representationReceiptsCountAsFreshAnalysis boundary ≡ false
representationNotAnalysis = refl

coresNotFabricated :
  Direct.analyticCoreInhabitanceFabricatedHere boundary ≡ false
coresNotFabricated = refl

rhStillOpen : Direct.rhDerived boundary ≡ false
rhStillOpen = refl
