module DASHI.Physics.Closure.Validation.RealizationProfileRigidityReport where

open import Agda.Builtin.String using (String)
open import Data.Maybe using (just)

open import DASHI.Physics.OrbitProfileData as OPD
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.ObservablePredictionPackage as OPP
open import DASHI.Physics.Closure.Validation.RealizationProfileRigidity as RPR

record RealizationProfileRigidityReport : Set where
  field
    reference : RPR.RealizationObservation
    candidate : RPR.RealizationObservation
    facts : RPR.MatchFacts reference candidate
    verdict : RPR.RigidityVerdict

record RealizationProfileRigiditySuite : Set where
  field
    selfReport : RealizationProfileRigidityReport
    admissibleReport : RealizationProfileRigidityReport
    negativeControlReport : RealizationProfileRigidityReport

record RealizationProfileRigidityAggregate : Set where
  field
    selfReport : RealizationProfileRigidityReport
    syntheticAdmissibleReport : RealizationProfileRigidityReport
    secondaryAdmissibleReport : RealizationProfileRigidityReport
    negativeControlReport : RealizationProfileRigidityReport

buildReport :
  (reference candidate : RPR.RealizationObservation) →
  RealizationProfileRigidityReport
buildReport reference candidate =
  let facts = RPR.computeFacts reference candidate
  in
  record
    { reference = reference
    ; candidate = candidate
    ; facts = facts
    ; verdict = RPR.classify facts
    }

observationFromObservablePackage :
  String →
  OPP.ObservablePredictionPackage →
  RPR.RealizationObservation
observationFromObservablePackage label observables =
  record
    { role = RPR.admissibleCandidate
    ; label = label
    ; orientationTag = just 31
    ; shell1Profile = OPD.shell1_p3_q1
    ; shell2Profile = OPD.shell2_p3_q1
    ; signature = just (OPP.ObservablePredictionPackage.provedSignature observables)
    }

observationFromMinimalClosure :
  String →
  MCPC.MinimalCrediblePhysicsClosure →
  RPR.RealizationObservation
observationFromMinimalClosure label closure =
  observationFromObservablePackage
    label
    (MCPC.MinimalCrediblePhysicsClosure.observables closure)

observationFromAdmissible :
  RPR.AdmissibleComparisonRealization →
  RPR.RealizationObservation
observationFromAdmissible = RPR.toObservation
