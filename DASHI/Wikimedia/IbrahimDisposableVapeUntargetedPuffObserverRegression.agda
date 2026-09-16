module DASHI.Wikimedia.IbrahimDisposableVapeUntargetedPuffObserverRegression where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.String using (String)

record UntargetedPuffObserverRegression : Set where
  constructor untargeted-puff-observer-regression
  field
    puffResolvedRequired : Bool
    aerosolDirectRequired : Bool
    broadUntargetedRequired : Bool
    wholeLifeDisposableRequired : Bool
    standardsSurfaceRequired : Bool
    keyMethodDOI : String
    standardsSurface : String
open UntargetedPuffObserverRegression public

requiredUntargetedPuffObserverRegression : UntargetedPuffObserverRegression
requiredUntargetedPuffObserverRegression = untargeted-puff-observer-regression
  true true true true true
  "10.1002/anse.202400079"
  "CORESTA Guide No. 39 (August 2026): Non-Targeted Analysis of Electronic Cigarette and Heated Tobacco Emissions"
