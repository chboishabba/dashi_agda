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
  "EPBC 2019/8575 is a controlled action with a source-paid s 130(1A) extension notice; authorised delegate and 1 October 2026 decision deadline are identified. The wider corpus now supplies same-landscape corridor/connectivity, historical vegetation, neighbouring proponent critical-habitat/removal evidence, restoration-lag evidence, local development pressure and offset-counterfactual leads, but these do not substitute for the exact 2019/8575 final-PD consumer record."
  "Extract the final Preliminary Documentation same-object matrix: exact action/clearing polygon, impacted and retained habitat by controlling matter, significance reasoning, avoidance/minimisation, residual impact, offsets, conservation-advice/recovery-plan correspondence and response-to-submissions; then bind those atoms to the actual Part 9 approval/refusal consumer."
  "1 October 2026"
  "controlled-action status, neighbouring-project evidence, corridor evidence and deadline do not equal refusal or protection; project-A facts cannot silently pay project-B atoms"

qldCriticalHabitat : RoadmapCoordinate
qldCriticalHabitat = roadmap-coordinate
  queenslandCriticalHabitatLane
  live
  "NCA s 13 rule is source-paid. The evidence graph now contains proponent-side Scenic/Peninsula use of a common approximately 675 ha contiguous-landscape carrier, Bellevue/Woogaroo Creek connectivity evidence, official broader corridor context, long-standing wooded-cover evidence, present-day observer occurrence/context evidence and project-specific critical-habitat/removal evidence at neighbouring fibres. The landscape-function case is therefore materially advanced, but the exact Springview parcel x habitat-function x essentiality join remains open."
  "Join the exact Springview/2019/8575 and cadastral/clearing polygons to primary habitat-function evidence, the shared corridor/contiguous-landscape carriers, Queensland habitat layers and any validated same-landscape occurrence evidence; then produce the s 13 same-parcel essentiality application receipt."
  "highest alpha before irreversible clearing; work concurrently with the s 102 works-threat lane"
  "federal/proponent use of 'critical habitat', neighbouring-project critical-habitat scores, citizen-science occurrence and image-backed neighbourhood correlation do not themselves pay Queensland s 13 essentiality"

qldInterim : RoadmapCoordinate
qldInterim = roadmap-coordinate
  queenslandInterimRestraintLane
  live
  "NCA ss 102-107 mechanism is source-paid. Development pressure is no longer abstract: 9281/2024/OW is an identified approved operational-works carrier expressly covering earthworks, vegetation clearing and stormwater, and 9293/2024/OW separately covers road work, drainage, stormwater and earthworks. Same-landscape habitat/corridor evidence is materially stronger, but the exact clearing drawing, commencement chronology and same-parcel detrimental-effect join remain open."
  "Acquire the approved 9281/2024/OW vegetation-clearing plans/drawings and current works chronology; intersect them with exact threatened-wildlife/habitat/corridor evidence and test the likely significant detrimental-effect requirements before preparing an interim conservation-order request."
  "now; before physical clearing or other irreversible works commence"
  "an approved clearing entitlement is not proof that clearing has commenced, and development pressure or habitat value alone does not establish the s 102 statutory conditions"

qldPermanent : RoadmapCoordinate
qldPermanent = roadmap-coordinate
  queenslandPermanentProtectionLane
  open
  "NCA s 49 compulsory nature-refuge route is source-paid, and the ecological/corridor corpus is stronger, but the qualifying s 13/area-of-major-interest basis and executive initiation coordinates are not yet paid."
  "Once the s 13 same-parcel function case is paid, compile exact parcels/tenure, refuge suitability, existing protection status and the ministerial/executive initiation package without waiting for every supporting advocacy lane."
  "prepare in parallel; activate immediately after the s 13 qualifying basis is sufficiently paid"
  "qualifying ecological evidence does not itself compel executive declaration or prove that a nature-refuge mechanism will be selected"

planningExemption : RoadmapCoordinate
planningExemption = roadmap-coordinate
  planningExemptionAuditLane
  live
  "Council material demonstrates mapped koala habitat can coexist with an approved/exempted development outcome. The local chain is now identified through 6243/2023/LAP, 4272/2020/ADP, 5547/2020/ADP, 7477/2022/ADP, 9281/2024/OW and 9293/2024/OW, exposing the exact approval/works objects that must be checked against the exemption history."
  "Recover the exact statutory grandfathering/exemption instrument, temporal scope, parcel scope and approval-history basis, then test whether each current ADP/operational-works component and variation still falls within that exemption."
  "parallel with federal/s 13/s 102 work; before relying on ordinary koala/planning prohibition arguments"
  "mapped habitat, a no-public-notification pathway, or an approved local DA does not by itself establish that the exemption is valid, current, invalid or exhausted"

politicalAdvocacy : RoadmapCoordinate
politicalAdvocacy = roadmap-coordinate
  politicalAdvocacyLane
  live
  "Federal Labor Minister/representatives, Queensland Labor opposition representative, Queensland LNP Environment Minister, and exact federal delegate are separately typed."
  "Keep advocacy role-correct and supporting only: evidence to delegate; portfolio escalation to Watt; electorate/community representation through Dick/Neumann/Mullen; NCA request to Powell. Do not divert evidence-acquisition effort from the legal consumers."
  "immediate through 1 October 2026 and for state-protection lane thereafter"
  "same-party alignment, public attention or celebrity support may affect routing but do not prove coordination, legal authority or bind any decision-maker"

enforcementBackstop : RoadmapCoordinate
enforcementBackstop = roadmap-coordinate
  enforcementBackstopLane
  open
  "EPBC s 475 and NCA s 173D mechanisms are source-paid as legal routes. Local operational-works approvals and the federal pending-decision state give concrete conduct/permission objects to monitor, but no contravention is presently inferred from those facts alone."
  "If works commence or are threatened, map the exact conduct, approval/permit/condition status and chronology to an exact statutory prohibition, condition, offence or other restraint basis before invoking court or enforcement mechanisms."
  "activate only if conduct threatens to outrun or breach applicable legal controls"
  "environmental harm, approval existence, project benefit or clearing entitlement alone is not automatically a statutory contravention"

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
