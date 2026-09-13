module DASHI.Empirical.DarkDimensionDESIDR2BAODataReceiptExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Empirical.DarkDimensionEmpiricalDiscriminationExact as Discrimination
import DASHI.Empirical.DarkDimensionSharedBAOObservationKeyExact as ObservationKey
import DASHI.Empirical.DarkDimensionSharedBAOObservableExact as SharedBAO
import DASHI.Empirical.GRQuantumPredictionProtocol as Prediction

record SignedDecimalRatio : Set where
  constructor signedDecimalRatio
  field
    negative : Bool
    magnitude : Discrimination.DecimalRatio

open SignedDecimalRatio public

ratio : Nat → Nat → Discrimination.DecimalRatio
ratio = Discrimination.decimalRatio

negativeThousandth : Nat → SignedDecimalRatio
negativeThousandth n = signedDecimalRatio true (ratio n 1000)

record AnisotropicBAOMeasurement
    (tracer : ObservationKey.DESIDR2TracerBin) : Set where
  constructor anisotropicBAOMeasurement
  field
    transverseKey : ObservationKey.SharedBAOObservationKey
    radialKey : ObservationKey.SharedBAOObservationKey
    transverseValue : Discrimination.DecimalRatio
    transverseUncertainty : Discrimination.DecimalRatio
    radialValue : Discrimination.DecimalRatio
    radialUncertainty : Discrimination.DecimalRatio
    withinBinCorrelation : SignedDecimalRatio

open AnisotropicBAOMeasurement public

mkMeasurement :
  (tracer : ObservationKey.DESIDR2TracerBin) →
  Nat → Nat → Nat → Nat → Nat →
  AnisotropicBAOMeasurement tracer
mkMeasurement tracer dm dmError dh dhError correlationMagnitude =
  anisotropicBAOMeasurement
    (ObservationKey.mkDR2Key tracer SharedBAO.transverseDMOverRd)
    (ObservationKey.mkDR2Key tracer SharedBAO.radialDHOverRd)
    (ratio dm 1000)
    (ratio dmError 1000)
    (ratio dh 1000)
    (ratio dhError 1000)
    (negativeThousandth correlationMagnitude)

lrg1Measurement : AnisotropicBAOMeasurement ObservationKey.lrg1
lrg1Measurement = mkMeasurement ObservationKey.lrg1 13587 169 21863 427 475

lrg2Measurement : AnisotropicBAOMeasurement ObservationKey.lrg2
lrg2Measurement = mkMeasurement ObservationKey.lrg2 17347 180 19458 332 423

lrg3Elg1Measurement : AnisotropicBAOMeasurement ObservationKey.lrg3Elg1
lrg3Elg1Measurement =
  mkMeasurement ObservationKey.lrg3Elg1 21574 153 17641 193 425

elg2Measurement : AnisotropicBAOMeasurement ObservationKey.elg2
elg2Measurement = mkMeasurement ObservationKey.elg2 27605 320 14178 217 437

qsoMeasurement : AnisotropicBAOMeasurement ObservationKey.qso
qsoMeasurement = mkMeasurement ObservationKey.qso 30519 758 12816 513 489

lyaMeasurement : AnisotropicBAOMeasurement ObservationKey.lya
lyaMeasurement = mkMeasurement ObservationKey.lya 38988 531 8632 101 431

record DESIDR2BAODataStatus : Set where
  constructor desiDR2BAODataStatus
  field
    publishedAnisotropicValuesRecorded : Bool
    marginalUncertaintiesRecorded : Bool
    withinBinCorrelationCoefficientRecorded : Bool
    fullCovarianceMatrixAssembled : Bool
    retrospectiveObservedData : Bool
    futureHeldOutData : Bool
    bothModelsNumericallyPredictedSameKeys : Bool
    likelihoodLocked : Bool

open DESIDR2BAODataStatus public

canonicalDESIDR2BAODataStatus : DESIDR2BAODataStatus
canonicalDESIDR2BAODataStatus =
  desiDR2BAODataStatus true true true false true false false false

withinBinCorrelationRecorded :
  withinBinCorrelationCoefficientRecorded canonicalDESIDR2BAODataStatus
  ≡ true
withinBinCorrelationRecorded = refl

fullCovarianceAssemblyStillOpen :
  fullCovarianceMatrixAssembled canonicalDESIDR2BAODataStatus ≡ false
fullCovarianceAssemblyStillOpen = refl

retrospectiveDataDoesNotPayHeldOutPrediction :
  futureHeldOutData canonicalDESIDR2BAODataStatus ≡ false
retrospectiveDataDoesNotPayHeldOutPrediction = refl

retrospectiveDataDoesNotPayDASHIDerivedPrediction :
  Prediction.quantitativePredictionDerived
    Prediction.canonicalPredictionBoundary
  ≡ false
retrospectiveDataDoesNotPayDASHIDerivedPrediction =
  Prediction.quantitativePredictionDerivedIsFalse
    Prediction.canonicalPredictionBoundary

desiDR2DOI : String
desiDR2DOI = "10.1103/tr6y-kpc6"
