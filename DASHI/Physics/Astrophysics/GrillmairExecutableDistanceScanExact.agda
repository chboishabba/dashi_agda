module DASHI.Physics.Astrophysics.GrillmairExecutableDistanceScanExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Finite executable scan surface for Grillmair-style matched filtering.
-- Tenths of a magnitude are represented by Nat offsets to avoid fake reals.
------------------------------------------------------------------------

record ScanBin : Set where
  constructor scan-bin
  field
    offsetTenthsMag : Nat
    matchedFilterScore : Nat
    projectionLabel : String
    reddeningControlPassed : Bool

open ScanBin public

record ScanSeries : Set where
  constructor scan-series
  field
    bins : List ScanBin
    stepTenthsMag : Nat
    sourceStepIsPointOneMag : Bool
    sourceStepIsPointOneMagIsTrue : sourceStepIsPointOneMag ≡ true

open ScanSeries public

record BestBinWitness : Set where
  constructor best-bin-witness
  field
    series : ScanSeries
    best : ScanBin
    bestIsMember : Bool
    bestIsMemberIsTrue : bestIsMember ≡ true
    noClaimOfExactPhysicalDistance : Bool
    noClaimOfExactPhysicalDistanceIsTrue : noClaimOfExactPhysicalDistance ≡ true

open BestBinWitness public

record DetectionPersistenceReceipt : Set where
  constructor detection-persistence-receipt
  field
    centralBin : ScanBin
    offsetThreeTenthsBin : ScanBin
    centralDetected : Bool
    displacedDetectionWeakens : Bool
    displacedDetectionWeakensIsTrue : displacedDetectionWeakens ≡ true
    sourceReference : String

open DetectionPersistenceReceipt public

record GrillmairExecutableScanBoundary : Set where
  constructor grillmair-executable-scan-boundary
  field
    largestScoreAutomaticallyConfirmsStream : Bool
    largestScoreAutomaticallyConfirmsStreamIsFalse : largestScoreAutomaticallyConfirmsStream ≡ false
    scanBinEqualsExactDistance : Bool
    scanBinEqualsExactDistanceIsFalse : scanBinEqualsExactDistance ≡ false
    projectionAndReddeningAreNuisanceFree : Bool
    projectionAndReddeningAreNuisanceFreeIsFalse : projectionAndReddeningAreNuisanceFree ≡ false

canonicalGrillmairExecutableScanBoundary : GrillmairExecutableScanBoundary
canonicalGrillmairExecutableScanBoundary =
  grillmair-executable-scan-boundary false refl false refl false refl
