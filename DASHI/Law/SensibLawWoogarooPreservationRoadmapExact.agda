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
  "EPBC 2019/8575 now has a substantially source-paid 2019 referral-era baseline: controlled-action status; Lot 9999 SP292760; 162 ha referral area; 136 ha stated impact; SHG 136 ha direct plus 26 ha indirect Koala-habitat impact; habitat score 7; Koala scat/food-tree evidence; connectivity score 2; rendered >500 ha habitat-connectivity map; rendered 136 ha critical-habitat impact map; SHG's Koala significant-impact conclusion; and a separate SHG proposition that approximately 136 ha GHFF foraging-habitat removal is likely to adversely impact habitat critical to survival. The uploaded file named Final-PD is only the one-page s 95B(2) publication notice: it pays 1,786 comments/publication, not the substantive final decision record."
  "First acquire the substantive 2026 Preliminary Documentation volumes/attachments and actual comment-summary/response carrier. Then perform the 2019-to-2026 delta audit: final action/clearing geometry, retained habitat, avoidance/alternatives, complete Koala/GHFF residual-impact analysis, final offsets, conservation-advice/recovery-plan treatment and changes responding to public comments; bind those final atoms to the Part 9 consumer."
  "1 October 2026"
  "publication notice is not substantive final PD; comment count is not response adequacy; SHG consultant evidence is not a Commonwealth finding; 2019 referral state is not automatically the unchanged 2026 state; a significant impact on habitat critical to survival does not automatically determine the Part 9 approval/refusal outcome"

qldInterim : RoadmapCoordinate
qldInterim = roadmap-coordinate
  queenslandInterimRestraintLane
  live
  "NCA ss 102-107 interim-conservation-order mechanism is source-paid. 9281/2024/OW and the supplied A12705838 negotiated approved plans provide a concrete approved vegetation-clearing/earthworks process and plan-scale works, bushfire-clearing, Open Space and Opossum/O'Dwyers interfaces. The Koala is qualifying threatened wildlife, so this route does not require a prior formal critical-habitat identification."
  "Pay the live statutory question: whether the qualifying threatened wildlife or another qualifying habitat/area is subject to the approved threatening process and whether significant detrimental effect is likely. Obtain a current independent ecological opinion and Condition 6(a)/prestart/commencement records. Use the existing local Ipswich monitoring, Ric Nattrass activity/corridor evidence and project ecology as distinct attributed inputs."
  "now; before physical clearing or other irreversible works commence"
  "perfect spatial overlap is not required; s 103(2) permits an order over land even if the wildlife/habitat is not on that land. Approval is not commencement; federal significant-impact reasoning is not the Queensland s 102 opinion; mitigation existence is not proof of mitigation effectiveness."

qldCriticalHabitat : RoadmapCoordinate
qldCriticalHabitat = roadmap-coordinate
  queenslandCriticalHabitatLane
  live
  "NCA s 13 is a statutory definition of critical habitat, not a standalone public 's 13 application' procedure. It defines critical habitat as habitat essential for conservation of a viable protected-wildlife population or native-wildlife community, including land not presently occupied. The definition can feed Ministerial opinion under s 102, nature-refuge reasoning under s 49, and formal identification through conservation plans or regulations."
  "Identify the relevant viable Koala population/community and test the without-Springview habitat counterfactual. In parallel identify the legally available route for asking the Minister to act on that evidence: s 102 opinion now, s 120H conservation-plan preparation or regulation-based identification where appropriate, and s 49 if nature-refuge prerequisites arise."
  "parallel with the live s 102 lane; do not treat s 13 itself as an application form or declaration mechanism"
  "habitat function, federal 'critical habitat', mapped corridors, activity records and genetic-cluster context may support the s 13 definition but do not themselves formally identify an area under a conservation plan/regulation or establish essentiality."

qldPermanent : RoadmapCoordinate
qldPermanent = roadmap-coordinate
  queenslandPermanentProtectionLane
  open
  "NCA s 49 compulsory nature-refuge route is source-paid. It requires failed agreement with relevant landholders plus a Ministerial opinion that the area is or includes an area of major interest or critical habitat and should be declared a nature refuge; the Governor in Council may then declare by regulation after objections are considered."
  "Prepare exact parcels/tenure, suitability, landholder/agreement history and the critical-habitat/area-of-major-interest evidence. Do not wait for a fictional s 13 application outcome: the relevant statutory predicate is the Minister's opinion under s 49, informed by the s 13 definition and evidence."
  "prepare behind the live s 102 and population-essentiality work"
  "s 13 is definitional, not a declaration by itself; ecological essentiality evidence does not establish the failed-agreement prerequisite or compel an s 49 declaration."

planningExemption : RoadmapCoordinate
planningExemption = roadmap-coordinate
  planningExemptionAuditLane
  live
  "The 2019 referral supplies a primary proponent statement of a Planning Regulation 2017 urban-purpose/urban-area vegetation-clearing exemption theory for least-concern/of-concern regulated vegetation, identifies a high-risk NCA protected-plants trigger area and states public notification was not required. Later Council material and the identified 6243/2023/LAP -> 4272/2020/ADP + 5547/2020/ADP -> 9281/2024/OW + 9293/2024/OW chain record the current approval sequence."
  "Recover the exact historical/current exemption and transition instruments; test vegetation-class, temporal, parcel, stage and variation predicates for every current component; distinguish the proponent's 2019 legal characterisation from current legal scope."
  "parallel with federal/s 102/population-essentiality work; before relying on ordinary koala/planning prohibition arguments"
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
  qldInterim
  qldCriticalHabitat
  qldPermanent
  true
  true
