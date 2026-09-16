module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseLTMDObservableSetAcquisitionValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseLTMDObservableSetAcquisitionExact as Acquisition

rmsdIsLTMDMonitored :
  Acquisition.ObservablePayment.ltmdMonitored Acquisition.rmsdOpenClosedObservation ≡ true
rmsdIsLTMDMonitored = refl

rmsdIsNotBEMetaBiasCV :
  Acquisition.ObservablePayment.beMetaBiasCV Acquisition.rmsdOpenClosedObservation ≡ false
rmsdIsNotBEMetaBiasCV = refl

thetaOneIsBEMetaBiasCV :
  Acquisition.ObservablePayment.beMetaBiasCV Acquisition.thetaOneObservation ≡ true
thetaOneIsBEMetaBiasCV = refl

threeCVDoesNotEqualWholeMonitoringSurface :
  Acquisition.AdKLTMDObservableSetBoundary.threeBEMetaCVsEqualWholeLTMDMonitoringSurface
    Acquisition.canonicalAdKLTMDObservableSetBoundary ≡ false
threeCVDoesNotEqualWholeMonitoringSurface = refl

identityMetadataDoesNotCreateRMSDDefinition :
  Acquisition.AdKLTMDObservableSetBoundary.identityMetadataCreatesRmsdMeasurement
    Acquisition.canonicalAdKLTMDObservableSetBoundary ≡ false
identityMetadataDoesNotCreateRMSDDefinition = refl
