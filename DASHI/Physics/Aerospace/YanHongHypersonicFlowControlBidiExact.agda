module DASHI.Physics.Aerospace.YanHongHypersonicFlowControlBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- YAN HONG / SUPERSONIC-HYPERSONIC FLOW CONTROL
--
-- Work identity is paid from NPU institutional material and exact publications.
-- Event identity is cross-welded only to the same named NPU professor/role.
-- None of this creates a common-cause or targeting claim.
------------------------------------------------------------------------

data YanHongFlowControlObject : Set where
  thermalExcitationShockControl
  plasmaActuatorAerospaceReview
  laserPlasmaFlowControlProgramme : YanHongFlowControlObject

record YanHongWorkReceipt : Set where
  constructor yan-hong-work-receipt
  field
    object : YanHongFlowControlObject
    title : String
    method : String
    sourceReference : String
    stableIdentifier : String
    primaryWorkObject : Bool

open YanHongWorkReceipt public

thermalExcitationMach5Receipt : YanHongWorkReceipt
thermalExcitationMach5Receipt = yan-hong-work-receipt
  thermalExcitationShockControl
  "Control of shock/boundary layer interaction in supersonic inlet using thermal excitation"
  "numerical Mach-5 inlet study varying heat-release power, actuator count and actuator-to-shock distance to control shock angle and boundary-layer separation"
  "Acta Aerodynamica Sinica 32(6), 2014, Yan Hong and Wang Song"
  "DOI 10.7638/kqdlxxb-2013.0102"
  true

plasmaActuatorReviewReceipt : YanHongWorkReceipt
plasmaActuatorReviewReceipt = yan-hong-work-receipt
  plasmaActuatorAerospaceReview
  "A Prospective of Plasma Actuators in Aerospace Engineering"
  "aerospace plasma-actuator mechanisms and applications; Yan Hong listed at NPU School of Power and Energy / aero-engine internal-aerodynamics laboratory"
  "Gas Physics 3(2), 2018, Joseph J. S. Shang, Hong Yan, Fan Liu"
  "DOI 10.19527/j.cnki.2096-1642.2018.02.001"
  true

laserPlasmaProgrammeReceipt : YanHongWorkReceipt
laserPlasmaProgrammeReceipt = yan-hong-work-receipt
  laserPlasmaFlowControlProgramme
  "NPU institutional research identity"
  "mechanisms, methods and applications of flow control for aerospace supersonic vehicles, especially laser-plasma flow control"
  "Northwestern Polytechnical University institutional profile/news material"
  "institutional work carrier"
  true

record YanHongEventWorkWeld : Set where
  constructor yan-hong-event-work-weld
  field
    eventPerson : String
    workPerson : String
    eventDate : String
    eventDescription : String
    eventSource : String
    sameInstitutionRoleBiography : Bool
    eventWorkSamePersonWeld : Bool
    causeCreatesTargetingInference : Bool

open YanHongEventWorkWeld public

yanHongEventWorkWeld : YanHongEventWorkWeld
yanHongEventWorkWeld = yan-hong-event-work-weld
  "Yan Hong / 严红"
  "Yan Hong / 严红, NPU School of Power and Energy professor"
  "2026-03-24 17:19"
  "NPU-sourced obituary reports death after illness at Jiangsu Provincial People's Hospital, age 57"
  "Northwestern Polytechnical University School of Power and Energy obituary, republished by ScienceNet 2026-03-26"
  true true false

record YanHongBoundary : Set where
  constructor yan-hong-boundary
  field
    hypersonicWorkMeansWeaponTargeting : Bool
    plasmaFlowControlMeansExoticPropulsion : Bool
    eventCauseImpliesCommonCause : Bool
    exactWorkObjectsMayInformStrategicFieldClassification : Bool

canonicalYanHongBoundary : YanHongBoundary
canonicalYanHongBoundary = yan-hong-boundary false false false true
