module DASHI.Reasoning.AuthorityBooleanPolarityRepairExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Biology.BodyMemoryMeasurementProxyBoundary as Measurement
import DASHI.Biology.FunctionalConnectomeBodyMemoryBridge as Functional
import DASHI.Biology.FMRIConnectomeProxyGovernance as FMRI
import DASHI.Biology.NeurochemicalBrainCarrierBridge as Neurochemical
import DASHI.Biology.NeurodivergentAtlasBodyMemoryBridge as Neurodivergent

------------------------------------------------------------------------
-- AUTHORITY-BOOLEAN POLARITY REPAIR
--
-- Several legacy biology records use names such as `mindReadingBlocked` while
-- instantiating the Boolean as `false`.  Their route-level semantics and prose
-- consistently mean that the corresponding authority is unavailable.
--
-- This owner does not mutate those legacy records.  It makes the authoritative
-- interpretation explicit and derives it from the existing inadmissible-route
-- witnesses.  New consumers should use this surface rather than interpreting
-- the polarity of the legacy `...Blocked` Boolean fields.
------------------------------------------------------------------------

measurementMindReadingAuthorityUnavailable :
  Measurement.AdmissibleBoundaryRoute Measurement.mindReadingRoute →
  Measurement.Never
measurementMindReadingAuthorityUnavailable = Measurement.mindReadingRouteRejected

measurementReverseInferenceAuthorityUnavailable :
  Measurement.AdmissibleBoundaryRoute Measurement.reverseInferenceRoute →
  Measurement.Never
measurementReverseInferenceAuthorityUnavailable = Measurement.reverseInferenceRouteRejected

measurementDiagnosisAuthorityUnavailable :
  Measurement.AdmissibleBoundaryRoute Measurement.diagnosisRoute →
  Measurement.Never
measurementDiagnosisAuthorityUnavailable = Measurement.diagnosisRouteRejected

measurementClinicalAuthorityUnavailable :
  Measurement.AdmissibleBoundaryRoute Measurement.clinicalAuthorityRoute →
  Measurement.Never
measurementClinicalAuthorityUnavailable = Measurement.clinicalAuthorityRouteRejected

functionalMindReadingAuthorityUnavailable :
  Functional.AdmissibleFunctionalConnectomeRoute Functional.mindReadingRoute →
  Functional.Never
functionalMindReadingAuthorityUnavailable = Functional.mindReadingRejected

functionalReverseInferenceAuthorityUnavailable :
  Functional.AdmissibleFunctionalConnectomeRoute Functional.reverseInferenceRoute →
  Functional.Never
functionalReverseInferenceAuthorityUnavailable = Functional.reverseInferenceRejected

functionalDiagnosisAuthorityUnavailable :
  Functional.AdmissibleFunctionalConnectomeRoute Functional.diagnosisRoute →
  Functional.Never
functionalDiagnosisAuthorityUnavailable = Functional.diagnosisRejected

functionalTreatmentAuthorityUnavailable :
  Functional.AdmissibleFunctionalConnectomeRoute Functional.treatmentRoute →
  Functional.Never
functionalTreatmentAuthorityUnavailable = Functional.treatmentRejected

functionalClinicalAuthorityUnavailable :
  Functional.AdmissibleFunctionalConnectomeRoute Functional.clinicalAuthorityRoute →
  Functional.Never
functionalClinicalAuthorityUnavailable = Functional.clinicalAuthorityRejected

fmriMindReadingAuthorityUnavailable :
  FMRI.AdmissibleFMRIConnectomeProxyRoute FMRI.mindReadingRoute →
  FMRI.Never
fmriMindReadingAuthorityUnavailable = FMRI.mindReadingRouteRejected

fmriReverseInferenceAuthorityUnavailable :
  FMRI.AdmissibleFMRIConnectomeProxyRoute FMRI.reverseInferenceBoundaryRoute →
  FMRI.Never
fmriReverseInferenceAuthorityUnavailable = FMRI.reverseInferenceBoundaryRouteRejected

fmriHiddenChartRecoveryAuthorityUnavailable :
  FMRI.AdmissibleFMRIConnectomeProxyRoute FMRI.hiddenChartRecoveryRoute →
  FMRI.Never
fmriHiddenChartRecoveryAuthorityUnavailable = FMRI.hiddenChartRecoveryRouteRejected

fmriDiagnosisAuthorityUnavailable :
  FMRI.AdmissibleFMRIConnectomeProxyRoute FMRI.diagnosisRoute →
  FMRI.Never
fmriDiagnosisAuthorityUnavailable = FMRI.diagnosisRouteRejected

fmriTreatmentAuthorityUnavailable :
  FMRI.AdmissibleFMRIConnectomeProxyRoute FMRI.treatmentRoute →
  FMRI.Never
fmriTreatmentAuthorityUnavailable = FMRI.treatmentRouteRejected

fmriClinicalAuthorityUnavailable :
  FMRI.AdmissibleFMRIConnectomeProxyRoute FMRI.clinicalAuthorityRoute →
  FMRI.Never
fmriClinicalAuthorityUnavailable = FMRI.clinicalAuthorityRouteRejected

record AuthorityBooleanPolarityRepair : Set where
  constructor authority-boolean-polarity-repair
  field
    bodyMeasurementMindReadingBlocked : Bool
    bodyMeasurementMindReadingBlockedIsTrue :
      bodyMeasurementMindReadingBlocked ≡ true

    bodyMeasurementReverseInferenceBlocked : Bool
    bodyMeasurementReverseInferenceBlockedIsTrue :
      bodyMeasurementReverseInferenceBlocked ≡ true

    bodyMeasurementDiagnosisBlocked : Bool
    bodyMeasurementDiagnosisBlockedIsTrue :
      bodyMeasurementDiagnosisBlocked ≡ true

    bodyMeasurementClinicalAuthorityBlocked : Bool
    bodyMeasurementClinicalAuthorityBlockedIsTrue :
      bodyMeasurementClinicalAuthorityBlocked ≡ true

    functionalConnectomeMindReadingBlocked : Bool
    functionalConnectomeMindReadingBlockedIsTrue :
      functionalConnectomeMindReadingBlocked ≡ true

    functionalConnectomeReverseInferenceBlocked : Bool
    functionalConnectomeReverseInferenceBlockedIsTrue :
      functionalConnectomeReverseInferenceBlocked ≡ true

    functionalConnectomeDiagnosisBlocked : Bool
    functionalConnectomeDiagnosisBlockedIsTrue :
      functionalConnectomeDiagnosisBlocked ≡ true

    functionalConnectomeTreatmentBlocked : Bool
    functionalConnectomeTreatmentBlockedIsTrue :
      functionalConnectomeTreatmentBlocked ≡ true

    functionalConnectomeClinicalAuthorityBlocked : Bool
    functionalConnectomeClinicalAuthorityBlockedIsTrue :
      functionalConnectomeClinicalAuthorityBlocked ≡ true

    fmriProxyMindReadingBlocked : Bool
    fmriProxyMindReadingBlockedIsTrue :
      fmriProxyMindReadingBlocked ≡ true

    fmriProxyReverseInferenceBlocked : Bool
    fmriProxyReverseInferenceBlockedIsTrue :
      fmriProxyReverseInferenceBlocked ≡ true

    fmriProxyHiddenChartRecoveryBlocked : Bool
    fmriProxyHiddenChartRecoveryBlockedIsTrue :
      fmriProxyHiddenChartRecoveryBlocked ≡ true

    fmriProxyDiagnosisBlocked : Bool
    fmriProxyDiagnosisBlockedIsTrue :
      fmriProxyDiagnosisBlocked ≡ true

    fmriProxyTreatmentBlocked : Bool
    fmriProxyTreatmentBlockedIsTrue :
      fmriProxyTreatmentBlocked ≡ true

    fmriProxyClinicalAuthorityBlocked : Bool
    fmriProxyClinicalAuthorityBlockedIsTrue :
      fmriProxyClinicalAuthorityBlocked ≡ true

    legacyBlockedBooleanPolarityInverted : Bool
    legacyBlockedBooleanPolarityInvertedIsTrue :
      legacyBlockedBooleanPolarityInverted ≡ true

    blockedMeansAuthorityUnavailable : Bool
    blockedMeansAuthorityUnavailableIsTrue :
      blockedMeansAuthorityUnavailable ≡ true

    legacyFalseMeansBlockedIsDeprecated : Bool
    legacyFalseMeansBlockedIsDeprecatedIsTrue :
      legacyFalseMeansBlockedIsDeprecated ≡ true

    auditedLegacyModules : List String
    interpretation : String

open AuthorityBooleanPolarityRepair public

canonicalAuthorityBooleanPolarityRepair : AuthorityBooleanPolarityRepair
canonicalAuthorityBooleanPolarityRepair = authority-boolean-polarity-repair
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  ("DASHI.Biology.BodyMemoryMeasurementProxyBoundary"
   ∷ "DASHI.Biology.FunctionalConnectomeBodyMemoryBridge"
   ∷ "DASHI.Biology.FMRIConnectomeProxyGovernance"
   ∷ "DASHI.Biology.NeurochemicalBrainCarrierBridge"
   ∷ "DASHI.Biology.NeurodivergentAtlasBodyMemoryBridge"
   ∷ [])
  "Authoritative polarity repair: blocked=true means the corresponding inference/diagnosis/treatment/clinical authority is unavailable. Legacy records whose field name says Blocked while the Boolean is false are retained only for compatibility; route inadmissibility/rejection owns the semantic boundary."

------------------------------------------------------------------------
-- Donor anchors retained so the repair cannot drift away from the actual
-- modules whose legacy Boolean polarity is being corrected.
------------------------------------------------------------------------

neurochemicalLegacySurfaceRetained : String
neurochemicalLegacySurfaceRetained =
  "DASHI.Biology.NeurochemicalBrainCarrierBridge retained; consume authority through the repaired boundary"

neurodivergentLegacySurfaceRetained : String
neurodivergentLegacySurfaceRetained =
  "DASHI.Biology.NeurodivergentAtlasBodyMemoryBridge retained; consume authority through the repaired boundary"
