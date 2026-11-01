module DASHI.Physics.Closure.Validation.SyntheticOneMinusAdmissible where

open import DASHI.Physics.Closure.Validation.RealizationProfileRigidity as RPR
open import DASHI.Physics.Closure.Validation.RealizationProfileRigidityReport as RPRR
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI
open import DASHI.Physics.Closure.Validation.SyntheticOneMinusOrientationSignatureBridge as SOSB
open import DASHI.Physics.SyntheticOneMinusShellRealization as SOM
open import DASHI.Physics.LorentzNeighborhoodDynamicCandidate as LNDC

syntheticReferenceObservation : RPR.RealizationObservation
syntheticReferenceObservation =
  RPRR.observationFromMinimalClosure
    "signed-permutation-shift"
    MCCSI.minimumCredibleClosureShift

syntheticAdmissibleCandidate : RPR.AdmissibleComparisonRealization
syntheticAdmissibleCandidate =
  record
    { label = LNDC.LorentzNeighborhoodDynamicCandidate.label LNDC.syntheticReady
    ; orientationTag = SOSB.syntheticOrientationTag
    ; shell1Profile = SOM.shell1Profile
    ; shell2Profile = SOM.shell2Profile
    ; signature = SOSB.syntheticSignature
    }

syntheticAdmissibleObservation : RPR.RealizationObservation
syntheticAdmissibleObservation =
  RPRR.observationFromAdmissible syntheticAdmissibleCandidate

syntheticAdmissibleReport : RPRR.RealizationProfileRigidityReport
syntheticAdmissibleReport =
  RPRR.buildReport syntheticReferenceObservation syntheticAdmissibleObservation

syntheticAdmissibleVerdict : RPR.RigidityVerdict
syntheticAdmissibleVerdict =
  RPRR.RealizationProfileRigidityReport.verdict syntheticAdmissibleReport
