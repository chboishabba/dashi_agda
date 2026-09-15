module DASHI.Wikimedia.IbrahimDisposableVapeLongitudinalAcquisitionRegression where

open import Agda.Builtin.Bool using (Bool; true)

record LongitudinalAcquisitionRegression : Set where
  constructor longitudinal-acquisition-regression
  field
    sameDeviceGateRequired : Bool
    puffResolvedGateRequired : Bool
    aerosolGateRequired : Bool
    broadOrganicNonTargetGateRequired : Bool
    nearMissLedgerRequired : Bool
    notLocatedNotNonexistentRequired : Bool
open LongitudinalAcquisitionRegression public

requiredLongitudinalAcquisitionRegression : LongitudinalAcquisitionRegression
requiredLongitudinalAcquisitionRegression = longitudinal-acquisition-regression
  true true true true true true
