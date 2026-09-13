module DASHI.Law.SensibLawWoogarooPreservationRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Law.SensibLawWoogarooPreservationLegalCutsetExact as Cutset
import DASHI.Law.SensibLawWoogarooDecisionMakerAndDelayLineageExact as Decision
import DASHI.Law.SensibLawWoogarooPoliticalAlignmentExact as Politics

------------------------------------------------------------------------
-- WOOGAROO PRESERVATION ROADMAP
--
-- This owner does not create new legal mechanisms. It reports the shortest
-- source/evidence/decision path through the already-owned cutset.
------------------------------------------------------------------------

data RoadmapState : Set where
  paid : RoadmapState
  live : RoadmapState
  open : RoadmapState
  blockedOnExternalDecision : RoadmapState

data RoadmapLane : Set where
  federalEPBC8575DecisionLane : RoadmapLane
  queenslandCriticalHabitatLane : RoadmapLane
  queenslandInterimRestraintLane : RoadmapLane
  queenslandPermanentProtectionLane : RoadmapLane
  planningExemptionAuditLane : RoadmapLane
  politicalAdvocacyLane : RoadmapLane
  enforcementBackstopLane : RoadmapLane
  custodianshipCommunityAuthorityLane : RoadmapLane

record RoadmapCoordinate : Set where
  constructor roadmap-coordinate
  field
    lane : RoadmapLane
    state : RoadmapState
    currentObject : String
    nextPayment : String
    deadlineOrTiming : String
    promotionBoundary : String

open RoadmapCoordinate public

federal8575 : RoadmapCoordinate
federal8575 = roadmap-coordinate
  federalEPBC8575DecisionLane
  live
  "EPBC 2019/8575 is a controlled action with a source-paid s 130(1A) extension notice; authorised delegate and 1 October 2026 decision deadline are identified."
  "Assemble exact species/community x habitat-loss x significance x avoidance/offset x conservation-advice matrix and submit/refine the refusal case against the actual Part 9 consumer."
  "1 October 2026"
  "controlled-action status and deadline do not equal refusal or protection"

qldCriticalHabitat : RoadmapCoordinate
qldCriticalHabitat = roadmap-coordinate
  queenslandCriticalHabitatLane
  open
  "NCA s 13 rule and candidate Woogaroo threatened-species/habitat evidence are source-paid at different fibres."
  "Produce a same-parcel application receipt showing why the exact habitat is essential for conservation of a viable protected-wildlife population or native-wildlife community."
  "highest alpha before irreversible clearing"
  "federal/proponent use of 'critical habitat' does not itself pay Queensland s 13"

qldInterim : RoadmapCoordinate
qldInterim = roadmap-coordinate
  queenslandInterimRestraintLane
  open
  "NCA ss 102-107 mechanism is source-paid; threatening-process application is not yet same-object paid."
  "Bind exact proposed works/timing to threatened wildlife or s 13 habitat and likely significant detrimental effect; prepare interim conservation-order request."
  "before works commence; delay window is useful but not protection"
  "project delay does not itself establish s 102 conditions"

qldPermanent : RoadmapCoordinate
qldPermanent = roadmap-coordinate
  queenslandPermanentProtectionLane
  open
  "NCA s 49 compulsory nature-refuge route is source-paid."
  "Pay s 13/area-of-major-interest basis, exact parcels/tenure, suitability, and ministerial initiation package."
  "parallel with federal decision lane"
  "qualifying evidence does not itself compel executive declaration"

planningExemption : RoadmapCoordinate
planningExemption = roadmap-coordinate
  planningExemptionAuditLane
  live
  "Council material demonstrates mapped koala habitat can coexist with an approved/exempted development outcome."
  "Recover the exact statutory grandfathering/exemption instrument, temporal scope, parcel scope, and whether later variations/components remain inside it."
  "before relying on ordinary koala/planning prohibition arguments"
  "mapped habitat does not factor to approval outcome without exemption/history coordinates"

politicalAdvocacy : RoadmapCoordinate
politicalAdvocacy = roadmap-coordinate
  politicalAdvocacyLane
  live
  "Federal Labor Minister/representatives, Queensland Labor opposition representative, Queensland LNP Environment Minister, and exact federal delegate are separately typed."
  "Run coordinated but role-correct advocacy: evidence to delegate; portfolio escalation to Watt; electorate/community representation through Dick/Neumann/Mullen; NCA request to Powell."
  "immediate through 1 October 2026 and for state-protection lane thereafter"
  "same-party alignment may ease routing but does not prove coordination or bind any decision-maker"

enforcementBackstop : RoadmapCoordinate
enforcementBackstop = roadmap-coordinate
  enforcementBackstopLane
  open
  "EPBC s 475 and NCA s 173D mechanisms are source-paid as legal routes."
  "Map any threatened conduct to an exact contravention/offence and standing/procedure before relying on court restraint."
  "activate if works threaten to outrun or breach applicable legal controls"
  "environmental harm alone is not automatically a statutory contravention"

custodianshipCommunity : RoadmapCoordinate
custodianshipCommunity = roadmap-coordinate
  custodianshipCommunityAuthorityLane
  open
  "Woogaroo stewardship owner preserves Country/community authority, permission, representation, ecological evidence and public advocacy as distinct coordinates."
  "Identify and source-pay any local custodial/community authority relevant to Country, knowledge, permission or stewardship without treating ecological evidence or Indigenous identity as mandate."
  "parallel; do not hold statutory ecology work hostage to unresolved authority claims"
  "custodianship/community authority is not automatically a common-law duty, EPBC test, or campaign mandate"

------------------------------------------------------------------------
-- Current shortest path to a physical preservation outcome.
------------------------------------------------------------------------

record HighestAlphaPath : Set where
  constructor highest-alpha-path
  field
    first : RoadmapCoordinate
    second : RoadmapCoordinate
    third : RoadmapCoordinate
    fourth : RoadmapCoordinate
    federalClockSourcePaid : Bool
    permanentProtectionStillOpen : Bool

currentHighestAlphaPath : HighestAlphaPath
currentHighestAlphaPath = highest-alpha-path
  federal8575
  qldCriticalHabitat
  qldInterim
  qldPermanent
  true
  true
