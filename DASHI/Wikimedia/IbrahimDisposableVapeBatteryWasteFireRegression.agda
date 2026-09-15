module DASHI.Wikimedia.IbrahimDisposableVapeBatteryWasteFireRegression where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

record RequiredBoundary : Set where
  constructor required-boundary
  field
    batteryWasteFiresPaid : Bool
    vapeSpecificEstimateKeptSeparate : Bool
    confirmedVersusSuspectedSeparated : Bool
    localIncidentCountsNotNationalized : Bool
    notRecordedNotZero : Bool

requiredBoundary : RequiredBoundary
requiredBoundary = required-boundary true true true true true
