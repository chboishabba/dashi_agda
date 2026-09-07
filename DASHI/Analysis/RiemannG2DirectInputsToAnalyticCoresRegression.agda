module DASHI.Analysis.RiemannG2DirectInputsToAnalyticCoresRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Analysis.RiemannG2DirectInputsToAnalyticCoresExact as Direct

private
  boundary = Direct.canonicalDirectInputsToAnalyticCoresBoundary

paymentDetourPruned :
  Direct.historicalPaymentDetourRequiredForSearch boundary ≡ false
paymentDetourPruned = refl

chosenOffCompilesCore :
  Direct.chosenCutoffOffRouteCompilesCurrentOffCore boundary ≡ true
chosenOffCompilesCore = refl

freshGammaCompilesCore :
  Direct.freshGammaRouteCompilesCurrentGammaCore boundary ≡ true
freshGammaCompilesCore = refl

representationNotPromoted :
  Direct.representationReceiptsPromotedToAnalysis boundary ≡ false
representationNotPromoted = refl

coresNotFabricated :
  Direct.analyticCoresInhabitedWithoutRouteInputs boundary ≡ false
coresNotFabricated = refl

rhStillOpen : Direct.rhDerived boundary ≡ false
rhStillOpen = refl
