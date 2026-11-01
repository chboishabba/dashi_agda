module DASHI.Wikimedia.IbrahimDisposableVapeSameDeviceLongitudinalRegression where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.String using (String)

record SameDeviceLongitudinalRegression : Set where
  constructor same-device-longitudinal-regression
  field
    samePhysicalDeviceRequired : Bool
    stageIndexedPuffLedgerRequired : Bool
    liquidAerosolPairingRequired : Bool
    unknownFeatureCorrespondenceRequired : Bool
    materialsAttributionRequired : Bool
    crossSectionNotLongitudinalRequired : Bool
    priorityExperiment : String
open SameDeviceLongitudinalRegression public

requiredSameDeviceLongitudinalRegression : SameDeviceLongitudinalRegression
requiredSameDeviceLongitudinalRegression = same-device-longitudinal-regression
  true true true true true true
  "same physical disposable: virgin baseline -> 100-puff indexed aerosol blocks -> mid-life paired liquid/aerosol -> late-life paired liquid/aerosol -> spent materials"
