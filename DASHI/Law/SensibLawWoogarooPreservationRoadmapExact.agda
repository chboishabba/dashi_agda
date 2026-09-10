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
  "EPBC 2019/8575 now has a substantially source-paid 2019 referral-era baseline: controlled-action status; Lot 9999 SP292760; 162 ha referral area; 136 ha stated impact; SHG 136 ha direct plus 26 ha indirect Koala-habitat impact; habitat score 7; Koala scat/food-tree evidence; connectivity score 2; rendered >500 ha habitat-connectivity map; rendered 136 ha critical-habitat impact map; and SHG's significant-impact conclusion. The current federal question is therefore a 2019-to-2026 final-state delta, not discovery of the historical project/habitat object."
  "Extract and compare the 2026 final Preliminary Documentation: final action/clearing geometry, retained habitat, avoidance/alternatives, complete residual-impact analysis, final offsets, conservation-advice/recovery-plan treatment and response-to-submissions; identify every material change from the 2019 baseline and bind the final atoms to the actual Part 9 consumer."
  "1 October 2026"
  "SHG consultant evidence is not a Commonwealth finding; 2019 referral state is not automatically the unchanged 2026 final-PD state; a significant impact on Koala habitat does not automatically determine the Part 9 approval/refusal outcome"

qldCriticalHabitat : RoadmapCoordinate
qldCriticalHabitat = roadmap-coordinate
  queenslandCriticalHabitatLane
  live
  "NCA s 13 now has strong same-Springview-parcel habitat-function evidence: Lot 9999 SP292760; mostly remnant vegetation; recognised Koala food trees; Koala scat evidence; Woogaroo/Opossum Creek function; SHG connectivity score 2 and >500 ha connectivity surface; habitat score 7; plus broader Scenic/Peninsula/Bellevue and official corridor context. The open issue is statutory viable-population/community essentiality, including stress-testing SHG's contrary recovery-value-0/site-not-viable reasoning."
  "Build the s 13 consumer around the exact parcel and current habitat function; identify the relevant viable protected-wildlife population/native-wildlife community; obtain expert analysis of severance/loss consequences; and test whether the NCA essentiality test is satisfied notwithstanding, or differently from, the 2019 EPBC recovery-value analysis."
  "highest alpha before irreversible clearing; work concurrently with the s 102 works-threat lane"
  "EPBC Koala-guideline 'critical habitat', habitat score 7, connectivity and occurrence do not themselves equal Queensland NCA s 13 statutory critical habitat or essentiality"

qldInterim : RoadmapCoordinate
qldInterim = roadmap-coordinate
  queenslandInterimRestraintLane
  live
  "NCA ss 102-107 mechanism is source-paid. 9281/2024/OW gives a concrete approved vegetation-clearing/earthworks object, while the same Springview project has a 2019 candidate habitat-impact surface: 136 ha habitat-score-7 Koala impact, food trees/scats and >500 ha connectivity. The operational/legal join remains incomplete because the EPBC impact map is not the 9281 clearing map and approval is not commencement."
  "Acquire the approved 9281 vegetation-clearing drawing/polygon, conditions and current works chronology; intersect that exact works geometry with current habitat/species/corridor evidence; then test likely significant detrimental effect and the procedural vehicle for an interim conservation order."
  "now; before physical clearing or other irreversible works commence"
  "2019 EPBC impact geometry is not the 9281 works geometry; an approved clearing entitlement is not proof of commencement or of the s 102 significant-detrimental-effect condition"

qldPermanent : RoadmapCoordinate
qldPermanent = roadmap-coordinate
  queenslandPermanentProtectionLane
  open
  "NCA s 49 compulsory nature-refuge route is source-paid and the exact-parcel ecological case is substantially stronger, but the qualifying s 13/area-of-major-interest basis, tenure/suitability and executive-initiation coordinates remain open."
  "Prepare exact parcels/tenure, suitability, existing protection status and initiation procedure now, then activate the permanent-protection package once the s 13/area-of-major-interest predicate is sufficiently paid."
  "prepare in parallel; activate immediately after the qualifying basis is sufficiently paid"
  "source-paid habitat value or even a successful s 13 evidentiary case does not itself create or compel an s 49 declaration"

planningExemption : RoadmapCoordinate
planningExemption = roadmap-coordinate
  planningExemptionAuditLane
  live
  "The 2019 referral supplies a primary proponent statement of a Planning Regulation 2017 urban-purpose/urban-area vegetation-clearing exemption theory for least-concern/of-concern regulated vegetation, identifies a high-risk NCA protected-plants trigger area and states public notification was not required. Later Council material and the identified 6243/2023/LAP -> 4272/2020/ADP + 5547/2020/ADP -> 9281/2024/OW + 9293/2024/OW chain record the current approval sequence."
  "Recover the exact historical/current exemption and transition instruments; test vegetation-class, temporal, parcel, stage and variation predicates for every current component; distinguish the proponent's 2019 legal characterisation from current legal scope."
  "parallel with federal/s 13/s 102 work; before relying on ordinary koala/planning prohibition arguments"
  "a proponent-stated historical exemption theory, mapped habitat, no-public-notification pathway or local approval does not by itself establish current exemption validity, invalidity or scope"

politicalAdvocacy : RoadmapCoordinate
politicalAdvocacy = roadmap-coordinate
  politicalAdvocacyLane
  live
  "Federal Minister/representatives, Queensland political representatives and the exact federal delegate are separately typed. The primary-evidence case is now materially stronger, so advocacy can carry a more precise evidence package without becoming a legal element itself."
  "Keep advocacy role-correct and supporting only: decision-grade evidence to the delegate; portfolio escalation to the Minister; representation/community routing separately; state-protection requests through the appropriate Queensland route."
  "immediate through 1 October 2026 and for state-protection lane thereafter"
  "political alignment, public attention or celebrity support may affect routing but do not prove coordination, legal authority, statutory satisfaction or bind a decision-maker"

enforcementBackstop : RoadmapCoordinate
enforcementBackstop = roadmap-coordinate
  enforcementBackstopLane
  open
  "EPBC s 475 and NCA enforcement mechanisms are source-paid as routes. Local works approvals, the federal pending-decision state and same-project ecology provide concrete objects to monitor, but no contravention is inferred merely from environmental harm, project benefit, habitat significance or clearing entitlement."
  "If works commence or are threatened, bind exact conduct, geometry, timing, approval/condition status and legal obligation before selecting injunction, enforcement, declaratory or judicial-review relief."
  "activate only if conduct threatens to outrun or breach applicable legal controls"
  "environmental harm, significant habitat impact, approval existence or clearing entitlement is not automatically a statutory contravention"

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
