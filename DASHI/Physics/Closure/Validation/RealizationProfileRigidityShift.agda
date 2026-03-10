module DASHI.Physics.Closure.Validation.RealizationProfileRigidityShift where

open import Agda.Builtin.String using (String)
open import Data.Maybe using (nothing)

open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Physics.OrbitProfileComputedBoolInv4 as OCB4
open import DASHI.Physics.OrbitProfileComputedTailPerm as OCTP
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI
open import DASHI.Physics.Closure.Validation.RealizationProfileRigidity as RPR
open import DASHI.Physics.Closure.Validation.RealizationProfileRigidityReport as RPRR
open import DASHI.Physics.Closure.Validation.SyntheticOneMinusAdmissible as SOA

referenceLabel : String
referenceLabel = "signed-permutation-shift"

tailPermLabel : String
tailPermLabel = "tail-permutation-negative-control"

boolInvLabel : String
boolInvLabel = "bool-inversion-admissible"

referenceObservation : RPR.RealizationObservation
referenceObservation =
  RPRR.observationFromMinimalClosure
    referenceLabel
    MCCSI.minimumCredibleClosureShift

referenceSelfReport : RPRR.RealizationProfileRigidityReport
referenceSelfReport =
  RPRR.buildReport referenceObservation referenceObservation

tailPermObservation : RPR.RealizationObservation
tailPermObservation =
  record
    { role = RPR.negativeControl
    ; label = tailPermLabel
    ; orientationTag = nothing
    ; shell1Profile = OCTP.shell1_p3_q1_tailperm_computed
    ; shell2Profile = OCTP.shell2_p3_q1_tailperm_computed
    ; signature = nothing
    }

tailPermReport : RPRR.RealizationProfileRigidityReport
tailPermReport =
  RPRR.buildReport referenceObservation tailPermObservation

tailPermVerdict : RPR.RigidityVerdict
tailPermVerdict =
  RPRR.RealizationProfileRigidityReport.verdict tailPermReport

boolInvCandidate : RPR.AdmissibleComparisonRealization
boolInvCandidate =
  record
    { label = boolInvLabel
    ; orientationTag = 31
    ; shell1Profile = OCB4.shell1_p3_q1_boolinv_computed
    ; shell2Profile = OCB4.shell2_p3_q1_boolinv_computed
    ; signature = CTI.sig31
    }

boolInvObservation : RPR.RealizationObservation
boolInvObservation =
  RPRR.observationFromAdmissible boolInvCandidate

boolInvReport : RPRR.RealizationProfileRigidityReport
boolInvReport =
  RPRR.buildReport referenceObservation boolInvObservation

boolInvVerdict : RPR.RigidityVerdict
boolInvVerdict =
  RPRR.RealizationProfileRigidityReport.verdict boolInvReport

rigiditySuite : RPRR.RealizationProfileRigiditySuite
rigiditySuite =
  record
    { selfReport = referenceSelfReport
    ; admissibleReport = SOA.syntheticAdmissibleReport
    ; negativeControlReport = tailPermReport
    }

rigidityAggregate : RPRR.RealizationProfileRigidityAggregate
rigidityAggregate =
  record
    { selfReport = referenceSelfReport
    ; syntheticAdmissibleReport = SOA.syntheticAdmissibleReport
    ; secondaryAdmissibleReport = boolInvReport
    ; negativeControlReport = tailPermReport
    }
