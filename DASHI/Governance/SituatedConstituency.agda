module DASHI.Governance.SituatedConstituency where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.IntersectionalLongitudinalResidualDynamics as Intersectional
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Situated constituency carrier.
--
-- Intersectionality precedent:
--   Kimberle Williams Crenshaw,
--   "Mapping the Margins: Intersectionality, Identity Politics, and Violence
--   against Women of Color", Stanford Law Review 43(6), 1991.
--   DOI: 10.2307/1229039.
--
-- The import is a carrier-level cross-pollination only.  It does not claim that
-- this module exhausts Crenshaw's account or that a finite axis list can replace
-- affected communities' own political articulation.
------------------------------------------------------------------------

data GovernanceAxis : Set where
  regionAxis : GovernanceAxis
  ruralUrbanAxis : GovernanceAxis
  displacementAxis : GovernanceAxis
  landAxis : GovernanceAxis
  ethnicityAxis : GovernanceAxis
  genderAxis : GovernanceAxis
  classAxis : GovernanceAxis
  religionAxis : GovernanceAxis
  colonialityAxis : GovernanceAxis
  armedPowerAxis : GovernanceAxis
  institutionalAccessAxis : GovernanceAxis
  disabilityAxis : GovernanceAxis
  sexualityAxis : GovernanceAxis
  neurotypeAxis : GovernanceAxis
  familyAxis : GovernanceAxis
  namedGovernanceAxis : String → GovernanceAxis

intersectionalAxisToGovernanceAxis :
  Intersectional.IntersectionalAxis →
  GovernanceAxis
intersectionalAxisToGovernanceAxis Intersectional.raceAxis = ethnicityAxis
intersectionalAxisToGovernanceAxis Intersectional.classAxis = classAxis
intersectionalAxisToGovernanceAxis Intersectional.genderAxis = genderAxis
intersectionalAxisToGovernanceAxis Intersectional.sexualityAxis = sexualityAxis
intersectionalAxisToGovernanceAxis Intersectional.disabilityAxis = disabilityAxis
intersectionalAxisToGovernanceAxis Intersectional.neurotypeAxis = neurotypeAxis
intersectionalAxisToGovernanceAxis Intersectional.religionAxis = religionAxis
intersectionalAxisToGovernanceAxis Intersectional.colonialityAxis = colonialityAxis
intersectionalAxisToGovernanceAxis Intersectional.lawAxis = institutionalAccessAxis
intersectionalAxisToGovernanceAxis Intersectional.landAxis = landAxis
intersectionalAxisToGovernanceAxis Intersectional.familyAxis = familyAxis
intersectionalAxisToGovernanceAxis Intersectional.institutionAxis = institutionalAccessAxis

canonicalGovernanceAxes : List GovernanceAxis
canonicalGovernanceAxes =
  regionAxis
  ∷ ruralUrbanAxis
  ∷ displacementAxis
  ∷ landAxis
  ∷ ethnicityAxis
  ∷ genderAxis
  ∷ classAxis
  ∷ religionAxis
  ∷ colonialityAxis
  ∷ armedPowerAxis
  ∷ institutionalAccessAxis
  ∷ []

record SituatedConstituency : Set where
  constructor situatedConstituency
  field
    constituencyLabel : String
    place : String
    historicalTime : Nat
    institution : String
    activeAxes : List GovernanceAxis
    representationState : String
    axisFreeRepresentation : Bool
    axisFreeRepresentationIsFalse :
      axisFreeRepresentation ≡ false

open SituatedConstituency public

mkSituatedConstituency :
  String →
  String →
  Nat →
  String →
  List GovernanceAxis →
  String →
  SituatedConstituency
mkSituatedConstituency label placeName time institutionName axes state =
  situatedConstituency
    label
    placeName
    time
    institutionName
    axes
    state
    false
    refl

neighbourhoodConstituency : SituatedConstituency
neighbourhoodConstituency =
  mkSituatedConstituency
    "neighbourhood constituency"
    "urban neighbourhood"
    2023
    "resistance committee / local council"
    (regionAxis
      ∷ ruralUrbanAxis
      ∷ classAxis
      ∷ genderAxis
      ∷ institutionalAccessAxis
      ∷ [])
    "locally deliberating and selecting representatives"

ruralConstituency : SituatedConstituency
ruralConstituency =
  mkSituatedConstituency
    "rural constituency"
    "rural locality"
    2023
    "local council / rural social formation"
    (regionAxis
      ∷ ruralUrbanAxis
      ∷ landAxis
      ∷ ethnicityAxis
      ∷ genderAxis
      ∷ colonialityAxis
      ∷ institutionalAccessAxis
      ∷ [])
    "self-representing rather than substituted by an urban proxy"

idpCampConstituency : SituatedConstituency
idpCampConstituency =
  mkSituatedConstituency
    "internally displaced persons camp constituency"
    "displacement camp"
    2023
    "camp committee / peace deliberation body"
    (regionAxis
      ∷ displacementAxis
      ∷ landAxis
      ∷ ethnicityAxis
      ∷ genderAxis
      ∷ armedPowerAxis
      ∷ institutionalAccessAxis
      ∷ [])
    "direct participant in peace, return, land and justice deliberation"

record AxisAwareRepresentationBoundary : Set where
  constructor axisAwareRepresentationBoundary
  field
    axisNeutralUniversalismClaimed : Bool
    ruralVoiceSubstitutedByUrbanElite : Bool
    displacementAxisEraseable : Bool
    landAxisEraseable : Bool
    affectedConstituencyMayArticulateAxes : Bool
    axisBundleIsExhaustiveClaimed : Bool

canonicalAxisAwareRepresentationBoundary :
  AxisAwareRepresentationBoundary
canonicalAxisAwareRepresentationBoundary =
  axisAwareRepresentationBoundary
    false
    false
    false
    false
    true
    false

canonicalSituatedConstituencyReceipt :
  GenericReceipt.GenericReceipt
canonicalSituatedConstituencyReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "situated constituency axis bundle"
    "DASHI.Governance.SituatedConstituency"
    "canonicalAxisAwareRepresentationBoundary"
    "ports the existing body/time/place/relation/institution/axis discipline into a public constituency carrier with explicit rural, displacement, land, coloniality and armed-power axes"
    "the axis list is non-exhaustive and cannot replace affected communities' own articulation or create representative authority"
    "agda -i . DASHI/Governance/SituatedConstituency.agda"
