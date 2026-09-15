module DASHI.Culture.MissingDeceasedTwentyScientistRound40CohortFrontierRefreshExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistRound23PromotionDebtRoadmapExact as R23
import DASHI.Culture.MissingDeceasedTwentyScientistRound39HCBAttributionSnowballExact as R39

------------------------------------------------------------------------
-- ROUND 40: COHORT-WIDE FRONTIER REFRESH
--
-- Rounds 31-39 deeply refined one HCB bridge family.  This owner widens back
-- to all twenty retained scientists and refreshes each row against the strongest
-- currently paid object surface.  A row changes only when a stronger source or
-- object coordinate was actually acquired.  Search attention alone is not an
-- evidence upgrade, and a stronger single-person object still cannot pay H2.
------------------------------------------------------------------------

record CohortFrontierRefresh : Set where
  constructor cohort-frontier-refresh
  field
    baseline : R23.PromotionDebt
    person : String
    strongestPaidObjectNow : String
    newlyPaidCoordinate : String
    attributionBoundary : String
    liveH1ToH2Debt : String
    exactSinglePersonObjectPaid : Bool
    secondRetainedPersonOnSameExactObjectPaid : Bool
    H2Paid : Bool
    H3Paid : Bool
    paretoPriorityNow : Nat

open CohortFrontierRefresh public

nuno40 : CohortFrontierRefresh
nuno40 = cohort-frontier-refresh R23.nuno
  "Nuno F. G. Loureiro"
  "VIRIATO exact HPC project; 50k core-hours on Curie + 50k on Hermit; named collaborator Alexander Schekochihin; later MIT PSFC/Viriato research surface"
  "exact project/resource/collaborator surface paid"
  "PRACE/MIT surfaces pay VIRIATO project identity and named collaborators only; they do not place another retained scientist on VIRIATO"
  "literal retained-person grant/work-package/facility/repository receipt on the same VIRIATO or successor object"
  true false false false 3

leblanc40 : CohortFrontierRefresh
leblanc40 = cohort-frontier-refresh R23.leblanc
  "NASA 40 kW Fission Surface Power I&C; WBS 658133.04.01.22.01.06; FICS executive/team roster"
  "exact WBS plus named FSP/FICS team surface paid"
  "NASA NTRS pays the webinar/WBS/team identities; the roster does not contain another retained scientist"
  "exact subordinate WBS, review, component, vendor or partner surface naming another retained scientist"
  true false false false 2

maiwald40 : CohortFrontierRefresh
maiwald40 = cohort-frontier-refresh R23.maiwald
  "JPL SURP SP23012 — Unambiguous Detection of Biosignatures by Action Spectroscopy; named PI/co-investigators and active cryogenic apparatus"
  "exact project team, apparatus and publication surface paid"
  "JPL SURP poster pays SP23012 identities/apparatus only; no retained second scientist is named"
  "shared JPL instrument, procurement, work package or project identifier naming another retained scientist"
  true false false false 2

reza40 : CohortFrontierRefresh
reza40 = cohort-frontier-refresh R23.reza
  "Mondaloy 200 → HCB/HBTD project; Monica Jacinto exact project-role relation paid"
  "exact Monica-to-HCB/Mondaloy project relation paid"
  "Round 39 keeps Monica project-role evidence separate from McCasland programme-reference evidence"
  "identity-bearing exact HCB task/contract receipt placing McCasland or another retained scientist on the same exact object"
  true false false false 1

grillmair40 : CohortFrontierRefresh
grillmair40 = cohort-frontier-refresh R23.grillmair
  "IPAC stellar-stream programme; Spitzer IRAC RR-Lyrae stream-distance project and named stream publications"
  "exact stream-project/facility/publication surfaces paid"
  "IPAC/publication surfaces pay Grillmair's stream objects and collaborators only; no retained second scientist is named"
  "survey/catalogue/project/facility identifier shared with another retained scientist"
  true false false false 3

hicks40 : CohortFrontierRefresh
hicks40 = cohort-frontier-refresh R23.hicks
  "JPL/CNEOS 3122 Florence optical lightcurve campaign; named observing collaborators and telescope network"
  "exact observing campaign/team surface paid"
  "JPL/CNEOS pays Florence campaign participation; no retained second scientist is named on that campaign"
  "observing-program, instrument, procurement or work-package identifier shared with another retained scientist"
  true false false false 3

mccasland40 : CohortFrontierRefresh
mccasland40 = cohort-frontier-refresh R23.mccasland
  "AFRL command chronology + personal contemporaneous HCB programme reference at AIAA SPACE 2013"
  "personal HCB programme-reference edge paid"
  "Round 39 keeps programme reference distinct from exact task/contract role"
  "literal 2011-2013 FA9300-07-C-0001/HCB/Mondaloy task, attendee, approval or contract-role receipt"
  true false false false 1

chavez40 : CohortFrontierRefresh
chavez40 = cohort-frontier-refresh R23.chavez
  "LANL DARHT + Scorpius accelerator engineering; Anthony Chavez identity paid by LANL"
  "same-person identity plus >25 years at DARHT and Scorpius design work paid"
  "LANL institutional publication pays Chavez identity and his DARHT/Scorpius work; it does not name another retained scientist on the same task"
  "DARHT/Scorpius task, work-package, drawing, review or facility receipt naming another retained scientist"
  true false false false 1

thomas40 : CohortFrontierRefresh
thomas40 = cohort-frontier-refresh R23.thomas
  "Novartis signalling/ferritinophagy assay objects"
  "no stronger exact cross-person object acquired in this refresh"
  "Round-23 object surface retained; search attention does not upgrade source payment"
  "literal grant/consortium/platform/vendor object naming another retained scientist"
  true false false false 4

amy40 : CohortFrontierRefresh
amy40 = cohort-frontier-refresh R23.amy
  "HAL5 Ning Li/Torr/AC Gravity reference + Holocron team surface + candidate NASA TM 20205010911 / SAA8-1519855"
  "Richard Eskridge team predicate, NASA candidate technical object, and archived 2020 statement locator paid separately"
  "predicate/chronology compatibility does not pay unnamed referent or paper identity"
  "identity-bearing Amy-origin or NASA review record linking Amy to the exact AC Gravity/Army/NASA object"
  true false false false 1

ning40 : CohortFrontierRefresh
ning40 = cohort-frontier-refresh R23.ning
  "DAAH01-01-9-R001 / Gravito-Electro Magnetic Superconductivity Experiment; official FY2001 report locator paid"
  "exact Army agreement/object locator paid; primary document bytes still unpaid"
  "secondary reproductions and locator do not substitute for primary SOW/closeout custody or a second retained-person role"
  "primary SOW/closeout/personnel/facility/apparatus source plus second retained-person same-object weld"
  true false false false 1

chen40 : CohortFrontierRefresh
chen40 = cohort-frontier-refresh R23.chen
  "NUDT Galaxy/Feiteng military-DSP lineage"
  "exact object family separated from Feng and Zhang Daibing objects"
  "same NUDT institution does not collapse distinct exact object families"
  "one exact NUDT/national task, codebase or work-package naming Chen plus another retained scientist"
  true false false false 2

feng40 : CohortFrontierRefresh
feng40 = cohort-frontier-refresh R23.feng
  "NUDT multi-aircraft collaborative air-combat planning / War Skull decision-science carrier"
  "exact air-combat planning object family paid"
  "object identity is local to Feng's source surface and does not transfer to Chen or Zhang Daibing"
  "one exact task/code/project/work-package naming Feng plus another retained scientist"
  true false false false 2

zhou40 : CohortFrontierRefresh
zhou40 = cohort-frontier-refresh R23.zhou
  "DICP DNL2200 high-performance polymer materials centre"
  "no stronger exact cross-person object acquired in this refresh"
  "Round-23 source role retained; later centre continuity remains non-promoting"
  "grant/patent/enterprise-transfer identifier shared with another retained scientist"
  true false false false 3

liu40 : CohortFrontierRefresh
liu40 = cohort-frontier-refresh R23.liu
  "Big Data Security Engineering Research Center / DSMM"
  "no stronger exact cross-person object acquired in this refresh"
  "Round-23 source role retained; governance transition is not task identity"
  "dated national project/task/company identifier shared with another retained scientist"
  true false false false 4

zhangXiaoxin40 : CohortFrontierRefresh
zhangXiaoxin40 = cohort-frontier-refresh R23.zhangXiaoxin
  "Fengyun / NSMC space-weather programme; FY-4C ionospheric-retrieval publication with explicit contribution roles"
  "exact Fengyun publication/team surface paid"
  "publication authorship and contribution roles do not place another retained scientist on the same Fengyun payload/project"
  "exact payload, instrument, project, funding or operations identifier shared with another retained scientist"
  true false false false 3

zhangDaibing40 : CohortFrontierRefresh
zhangDaibing40 = cohort-frontier-refresh R23.zhangDaibing
  "NUDT autonomous-UAV landing / multi-sensor guidance object"
  "exact UAV object family separated from Chen/Feng objects"
  "same NUDT institution and military relevance remain too coarse for shared-task identity"
  "one exact unmanned-systems task/code/project naming Zhang Daibing plus another retained scientist"
  true false false false 2

liMinyong40 : CohortFrontierRefresh
liMinyong40 = cohort-frontier-refresh R23.liMinyong
  "photopharmacology / fluorescent-probe patent family"
  "no stronger exact cross-person object acquired in this refresh"
  "Round-23 patent-family surface retained; post-loss custody does not create cause or shared programme identity"
  "grant/project/patent co-custody identifier shared with another retained scientist"
  true false false false 4

fang40 : CohortFrontierRefresh
fang40 = cohort-frontier-refresh R23.fang
  "Inverse design of phononic meta-structured materials; explicit multi-institution publication team including Fang Daining"
  "exact publication/team surface paid"
  "publication coauthorship does not itself place another retained scientist on the same national project/work package"
  "national project/grant/work-package identifier shared with another retained scientist or paid cross-institution object"
  true false false false 2

yan40 : CohortFrontierRefresh
yan40 = cohort-frontier-refresh R23.yan
  "NPU hypersonic thermal/plasma flow-control carrier"
  "no stronger exact cross-person object acquired in this refresh"
  "Round-23 object surface retained; strategic aerospace relevance remains H1-only"
  "exact national/NPU project, facility, grant or test identifier shared with another retained scientist"
  true false false false 3

round40All : List CohortFrontierRefresh
round40All =
  nuno40 ∷ leblanc40 ∷ maiwald40 ∷ reza40 ∷ grillmair40 ∷ hicks40 ∷
  mccasland40 ∷ chavez40 ∷ thomas40 ∷ amy40 ∷ ning40 ∷ chen40 ∷ feng40 ∷
  zhou40 ∷ liu40 ∷ zhangXiaoxin40 ∷ zhangDaibing40 ∷ liMinyong40 ∷ fang40 ∷ yan40 ∷ []

round40FrontierCount : Nat
round40FrontierCount = 20

round40H2PaidCount : Nat
round40H2PaidCount = 0

round40H3PaidCount : Nat
round40H3PaidCount = 0

chavezIdentityPaid : Bool
chavezIdentityPaid = true

leblancExactTeamSurfacePaid : Bool
leblancExactTeamSurfacePaid = true

maiwaldExactProjectTeamPaid : Bool
maiwaldExactProjectTeamPaid = true

hicksExactCampaignTeamPaid : Bool
hicksExactCampaignTeamPaid = true

nunoExactViriatoProjectPaid : Bool
nunoExactViriatoProjectPaid = true

grillmairExactStreamProjectPaid : Bool
grillmairExactStreamProjectPaid = true

fangExactPublicationTeamPaid : Bool
fangExactPublicationTeamPaid = true

zhangXiaoxinExactFengyunPaperPaid : Bool
zhangXiaoxinExactFengyunPaperPaid = true

crossPersonH2RequiresRetainedPersonOnSameExactObject : Bool
crossPersonH2RequiresRetainedPersonOnSameExactObject = true

strongerSinglePersonObjectDoesNotPayH2 : Bool
strongerSinglePersonObjectDoesNotPayH2 = true

searchAttentionDoesNotUpgradeEvidence : Bool
searchAttentionDoesNotUpgradeEvidence = true

sourceRoleJoinStillCannotTransferClaim : Bool
sourceRoleJoinStillCannotTransferClaim = true

round40TierA : String
round40TierA = "Reza/McCasland: both sides now have HCB payments at different granularities; one contemporaneous McCasland exact-task/contract/Mondaloy role receipt remains the shortest H2 path."

round40TierB : String
round40TierB = "Ning, Amy, Chavez: exact single-person programme/object surfaces are strong; acquire primary identity-bearing cross-person welds. Chavez identity itself is no longer a debt."

round40TierC : String
round40TierC = "LeBlanc, Maiwald/Hicks, Chen/Feng/Zhang Daibing: exact teams or object families exist; search for one retained-person crossing identifier rather than more institution-level overlap."

round40TierD : String
round40TierD = "Nuno, Grillmair, Fang, Zhang Xiaoxin, Zhou, Liu, Li Minyong, Yan, Thomas: continue grant/project/facility/payload/patent/work-package identifiers; stronger single-person detail alone cannot pay H2."

round40Pareto : String
round40Pareto = "Whole-cohort frontier: Reza/McCasland first; Ning/Amy/Chavez next; then LeBlanc, JPL and NUDT crossing identifiers; then remaining exact-ID snowballs. H3 remains inadmissible until a literal two-retained-person same-object H2 receipt is paid."
