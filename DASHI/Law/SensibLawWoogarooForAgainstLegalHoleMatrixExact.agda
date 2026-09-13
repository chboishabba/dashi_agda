module DASHI.Law.SensibLawWoogarooForAgainstLegalHoleMatrixExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- WOOGAROO FOR / AGAINST LEGAL-HOLE MATRIX
--
-- This owner is a counsel-handoff audit.  It does not decide legal merits.
-- Each route is tested against both the strongest presently sourced support
-- and the strongest presently sourced defeating/limiting coordinate.
------------------------------------------------------------------------

data HoleStatus : Set where
  closed : HoleStatus
  partiallyClosed : HoleStatus
  open : HoleStatus

data LegalLane : Set where
  epbc8575ApprovalRefusal : LegalLane
  qldNCA13CriticalHabitat : LegalLane
  qldNCA102InterimOrder : LegalLane
  qldNCA49NatureRefuge : LegalLane
  qldPart7APlanningConstraint : LegalLane
  epbc475Injunction : LegalLane
  planningGrandfatheringExemption : LegalLane
  cumulativeCorridorFragmentation : LegalLane

record ForAgainstHole : Set where
  constructor for-against-hole
  field
    lane : LegalLane
    support : String
    strongestCounter : String
    status : HoleStatus
    missingPayment : String
    conclusionAlreadyProved : Bool

open ForAgainstHole public

epbc8575Hole : ForAgainstHole
epbc8575Hole = for-against-hole
  epbc8575ApprovalRefusal
  "Controlled-action status, ss 18/18A threatened-species/community controlling provisions, Preliminary Documentation assessment, exact delegate, and 1 October 2026 decision clock are source-paid. EPBC ss 136 and 139 require the decision-maker to consider protected-matter material and, where significant impact on a listed threatened species/community is engaged, approved conservation advice."
  "Approval remains discretionary within the statutory Part 9 framework; s 136 expressly requires economic and social matters to be considered as well. Controlled-action status does not imply refusal, and conditions under s 134 may be used instead of refusal where lawfully sufficient."
  partiallyClosed
  "Primary project ecology/impact/avoidance/offset material must still be extracted and tested against the exact Part 9 decision record; counsel must assess whether refusal is legally compelled, merely open, or weaker than a conditioned approval."
  false

qld13Hole : ForAgainstHole
qld13Hole = for-against-hole
  qldNCA13CriticalHabitat
  "NCA s 13 defines critical habitat as habitat essential for conservation of a viable population of protected wildlife or a community of native wildlife, including land not presently occupied. Threatened species, remnant habitat, corridor/connectivity and fragmentation evidence are relevant candidates."
  "Species presence, habitat mapping, Commonwealth 'critical habitat' terminology, and a Statewide Biodiversity Corridor do not themselves establish s 13 essentiality. The same-object essentiality/viability proposition remains evidentially unclosed."
  partiallyClosed
  "Exact parcel x habitat-function x population-viability evidence, preferably supported by expert ecology and exact GIS intersection."
  false

qld102Hole : ForAgainstHole
qld102Hole = for-against-hole
  qldNCA102InterimOrder
  "NCA s 102 permits an interim conservation order where threatened/near-threatened wildlife, critical habitat, an area of major interest or protected area is subject to a threatening process likely to have significant detrimental effect; s 103 permits prohibition/control of the process."
  "The power is discretionary ('may'), depends on the Minister forming the required opinion, and the current evidence does not yet bind exact works/timing to a likely significant detrimental effect. An order is temporary: s 105 caps the initial order at 60 days, with extension by Governor in Council of no more than 90 days."
  partiallyClosed
  "Part Aii clearing directions/works chronology + exact affected habitat/wildlife + expert detrimental-effect evidence + procedural request route."
  false

qld49Hole : ForAgainstHole
qld49Hole = for-against-hole
  qldNCA49NatureRefuge
  "NCA s 49 allows a compulsory nature-refuge process where Minister and landholders cannot agree and the Minister considers the area to include an area of major interest or critical habitat and that it should be declared a nature refuge."
  "The route is not a unilateral campaign application: inability to agree, ministerial opinion, notice, objections, and eventual Governor in Council regulation are built into the section. It is discretionary and procedurally heavier than an emergency restraint route."
  partiallyClosed
  "Exact tenure/interests, s 13 or area-of-major-interest basis, evidence of the proposal/agreement pathway and inability to agree, plus ministerial/Governor-in-Council strategy."
  false

part7AHole : ForAgainstHole
part7AHole = for-against-hole
  qldPart7APlanningConstraint
  "NCA Part 7A s 126A prevents local government from granting approvals inconsistent with a regulation identifying land as or including critical habitat/area of major interest. NCA s 123 similarly constrains local-government decisions where a conservation plan identifies such land."
  "This only bites once the relevant land is actually identified by the required regulation or conservation plan. General habitat mapping, corridor mapping or an unformalised s 13 argument is not enough. Earlier approvals/grandfathering also require separate analysis."
  partiallyClosed
  "Identify whether any current regulation/conservation plan covers the exact land; otherwise assess the practical route to obtain such identification and its effect on already-existing approvals."
  false

epbc475Hole : ForAgainstHole
epbc475Hole = for-against-hole
  epbc475Injunction
  "EPBC s 475 permits the Minister or an interested person to seek a Federal Court injunction against conduct constituting an offence or other contravention of the Act/regulations, including proposed conduct."
  "Environmental harm alone is insufficient. The exact future conduct must constitute a specific offence/contravention, and interested-person standing plus procedural/cost issues remain to be assessed. A lawful approved action taken in accordance with conditions is not automatically enjoinable merely because it damages habitat."
  partiallyClosed
  "Map threatened conduct to an exact EPBC offence/contravention and preserve standing/evidence before works commence."
  false

planningExemptionHole : ForAgainstHole
planningExemptionHole = for-against-hole
  planningGrandfatheringExemption
  "Council material expressly records mapped koala habitat and an approved/exempted development outcome, proving that the exemption/history coordinate is legally material."
  "The exact statutory/planning instrument, temporal scope, parcel/stage scope and effect of later amendments have not yet been recovered. Without that instrument we cannot prove either that the exemption defeats the current case or that it has ceased to apply."
  open
  "Primary exemption/grandfathering instrument + approval history + current project/stage comparison."
  false

corridorHole : ForAgainstHole
corridorHole = for-against-hole
  cumulativeCorridorFragmentation
  "Official Queensland Statewide Biodiversity Corridor mapping and the campaign aerial outline create a strong same-landscape hypothesis for connectivity/fragmentation across Springview, Scenic and Peninsular; this can be legally relevant to EPBC protected-matter impacts and factually relevant to NCA s 13 essentiality."
  "The screenshots are not georeferenced to each other, project boundaries belong to distinct referrals, and corridor designation is not itself a statutory conclusion of significant impact or critical habitat."
  open
  "Exact polygons for each project x official machine-readable corridor geometry x expert ecological function/severance evidence, kept project-indexed before any cumulative inference."
  false

------------------------------------------------------------------------
-- Global boundary: none of the ultimate merits/outcomes is presently proved.
------------------------------------------------------------------------

record LegalHoleAuditSummary : Set where
  constructor legal-hole-audit-summary
  field
    legalMechanismsIdentified : Bool
    keyStatutoryTestsIdentified : Bool
    mainDefeatersIdentified : Bool
    allEvidenceHolesClosed : Bool
    refusalLegallyCompelledProved : Bool
    qldCriticalHabitatProved : Bool
    interimOrderEntitlementProved : Bool
    permanentProtectionEntitlementProved : Bool

currentAudit : LegalHoleAuditSummary
currentAudit = legal-hole-audit-summary
  true
  true
  true
  false
  false
  false
  false
  false
