module DASHI.Physics.CondensedMatter.MATBGGeometryCaloricUpperBoundReceiptExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record GeometryCaloricUpperBoundReceipt : Set where
  constructor geometry-caloric-upper-bound-receipt
  field
    scriptPath : String
    evidencePath : String
    scriptSHA256 : String
    entropySourceDOI : String
    filling0DeltaSOverKB : String
    filling1DeltaSOverKB : String
    filling2DeltaSOverKB : String
    filling3DeltaSOverKB : String
    filling1TDeltaS15KMeVPerCell : String
    assertionsPassed : Bool

open GeometryCaloricUpperBoundReceipt public

canonicalGeometryCaloricUpperBoundReceipt : GeometryCaloricUpperBoundReceipt
canonicalGeometryCaloricUpperBoundReceipt =
  geometry-caloric-upper-bound-receipt
    "scripts/matbg_geometry_caloric_upper_bound.py"
    "Docs/evidence/matbg_geometry_caloric_upper_bound_2026-10-16.json"
    "263011eaecf0135634a087f4f8c0b1e47d247143fc347db5cb4138f3b71a60f7"
    "10.1038/s41467-026-76179-y"
    "4.248495242049359"
    "2.6390573296152584"
    "1.540445040947149"
    "0.6931471805599453"
    "3.4112454760227697"
    true

record GeometryCaloricUpperBoundBoundary : Set where
  constructor geometry-caloric-upper-bound-boundary
  field
    sourceCombinatorialEntropyUsed : Bool
    entropySwingExecutionPaid : Bool
    equilibriumTDeltaSScalePaid : Bool
    controlledGeometryCyclePaid : Bool
    reversibleCyclePaid : Bool
    adiabaticTemperatureChangePaid : Bool
    usefulCoolingPaid : Bool
    copPaid : Bool
    hysteresisRelaxationClosurePaid : Bool
    sameSampleQTMEntropyCyclePaid : Bool

open GeometryCaloricUpperBoundBoundary public

canonicalGeometryCaloricUpperBoundBoundary : GeometryCaloricUpperBoundBoundary
canonicalGeometryCaloricUpperBoundBoundary =
  geometry-caloric-upper-bound-boundary
    true true true false false false false false false false

record GeometryCaloricAttributionBoundary : Set where
  constructor geometry-caloric-attribution-boundary
  field
    zhangOwnsObservedEntropyAndStrainInterpretation : Bool
    dashiOwnsTDeltaSDiagnostic : Bool
    equilibriumEntropyDifferenceDoesNotProveActuatedCaloricCycle : Bool

open GeometryCaloricAttributionBoundary public

canonicalGeometryCaloricAttributionBoundary : GeometryCaloricAttributionBoundary
canonicalGeometryCaloricAttributionBoundary =
  geometry-caloric-attribution-boundary true true true
