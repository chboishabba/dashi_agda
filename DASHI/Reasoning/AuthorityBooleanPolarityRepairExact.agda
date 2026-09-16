module DASHI.Reasoning.AuthorityBooleanPolarityRepairExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Biology.BodyMemoryMeasurementProxyBoundary as Measurement
import DASHI.Biology.FunctionalConnectomeBodyMemoryBridge as Functional
import DASHI.Biology.FMRIConnectomeProxyGovernance as FMRI

------------------------------------------------------------------------
-- AUTHORITY-BOOLEAN POLARITY REPAIR
--
-- Some legacy biology records use names such as `mindReadingBlocked` while
-- storing `false`, even though their route-level semantics make the prohibited
-- route uninhabitable.  New consumers should derive authority from the route
-- rejection witnesses and use positive `blocked = true` semantics here.
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
    fmriProxyMindReadingBlocked : Bool
    fmriProxyMindReadingBlockedIsTrue :
      fmriProxyMindReadingBlocked ≡ true
    fmriProxyReverseInferenceBlocked : Bool
    fmriProxyReverseInferenceBlockedIsTrue :
      fmriProxyReverseInferenceBlocked ≡ true
    fmriProxyHiddenChartRecoveryBlocked : Bool
    fmriProxyHiddenChartRecoveryBlockedIsTrue :
      fmriProxyHiddenChartRecoveryBlocked ≡ true
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
  ("DASHI.Biology.BodyMemoryMeasurementProxyBoundary"
   ∷ "DASHI.Biology.FunctionalConnectomeBodyMemoryBridge"
   ∷ "DASHI.Biology.FMRIConnectomeProxyGovernance"
   ∷ [])
  "Authority is derived from the existing rejected/inadmissible routes. Legacy fields whose name says Blocked while the Boolean is false are compatibility metadata only; new consumers use blocked=true to mean the authority is unavailable."
