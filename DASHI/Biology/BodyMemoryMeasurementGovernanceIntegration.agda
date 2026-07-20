module DASHI.Biology.BodyMemoryMeasurementGovernanceIntegration where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.BodyMemoryMeasurementProxyBoundary as BodyProxy
import DASHI.Biology.FMRIConnectomeProxyGovernance as FMRI
import DASHI.Promotion.MeasurementProxyBoundaryCore as Measurement

record BodyMemoryMeasurementGovernanceIntegration : Set where
  constructor mkBodyMemoryMeasurementGovernanceIntegration
  field
    label : String
    sharedMeasurementBoundary : Measurement.MeasurementProxyBoundary
    fmriGovernance : FMRI.FMRIConnectomeProxyGovernance
    bodyProxyBoundaryImported : Bool
    measurementIsNotHiddenChart : Bool
    proxyIsNotCause : Bool
    neuralProxyIsNotMindReading : Bool
    measurementIsNotDiagnosis : Bool
    diagnosisIsNotTreatmentAuthority : Bool
    integrationHolds : Bool
    integrationHoldsIsTrue : integrationHolds ≡ true

open BodyMemoryMeasurementGovernanceIntegration public

canonicalBodyMemoryMeasurementGovernanceIntegration : BodyMemoryMeasurementGovernanceIntegration
canonicalBodyMemoryMeasurementGovernanceIntegration =
  mkBodyMemoryMeasurementGovernanceIntegration
    "body-memory measurement governance integration"
    Measurement.canonicalMeasurementProxyBoundary
    FMRI.canonicalFMRIConnectomeProxyGovernance
    true true true true true true true refl
