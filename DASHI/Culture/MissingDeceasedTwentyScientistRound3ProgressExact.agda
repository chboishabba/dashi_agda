module DASHI.Culture.MissingDeceasedTwentyScientistRound3ProgressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- THIRD TWENTY-SCIENTIST ROUND
--
-- Every retained scientist is touched again.  This round makes a further
-- distinction between genuine post-loss capability succession and stale/frozen
-- institutional manifestations that continue to display a deceased person's
-- name.  Search residuals remain residuals; technical adjacency remains
-- non-promoting.
------------------------------------------------------------------------

data Round3Side : Set where us china : Round3Side

data Round3ResultKind : Set where
  primaryPromotion boundedPromotion searchResidual controlStrengthening staleSurfaceDiscriminator : Round3ResultKind

record Round3Progress : Set where
  constructor round3-progress
  field
    person : String
    side : Round3Side
    searchTarget : String
    resultKind : Round3ResultKind
    sourceReference : String
    freshDelta : String
    nextExactLeaf : String
    leafPaid : Bool

open Round3Progress public

------------------------------------------------------------------------
-- United States scientific cohort (11)
------------------------------------------------------------------------

nunoLoureiroRound3 : Round3Progress
nunoLoureiroRound3 = round3-progress
  "Nuno F. G. Loureiro" us
  "exact Viriato/KREHM repository, grant, student and simulation-state handover"
  searchResidual
  "targeted MIT/PSFC and repository search this round"
  "no new source-exact Viriato/KREHM repository or grant-transfer object surfaced beyond the already paid memorial/student continuity surfaces"
  "named same-work repository/grant/advisor/simulation-state transfer for Viriato/KREHM"
  false

joshuaLeBlancRound3 : Round3Progress
joshuaLeBlancRound3 = round3-progress
  "Joshua Kyle LeBlanc" us
  "first actual post-loss SNP I&C TechMat roster and handover"
  staleSurfaceDiscriminator
  "NASA NTRS 20250008475, acquired 2025-08-16, webinar 2025-08-26, last modified 2026-07-16"
  "the public NASA object still names LeBlanc as SNP I&C TechMat Team Lead after his death and even after later repository maintenance; this strengthens the stale/frozen-manifestation discriminator rather than paying succession"
  "first dated TechMat roster revision, named successor/handover and qualification/calibration/failure-data custody transfer"
  false

frankMaiwaldRound3 : Round3Progress
frankMaiwaldRound3 = round3-progress
  "Frank W. Maiwald" us
  "raw/reduced action-spectroscopy data, calibration, notebook and formal PI-handover custody"
  searchResidual
  "targeted JPL SURP/action-spectroscopy search this round"
  "no new primary custody object improved on the paid 2023 Maiwald to 2024/2025 Nemchick manifestation succession"
  "administrative PI-change/handover record and exact dataset/calibration/notebook/publication crosswalk"
  false

monicaRezaRound3 : Round3Progress
monicaRezaRound3 = round3-progress
  "Monica Jacinto / Monica Reza" us
  "event-time JPL role and patent/programme custody from Boeing/UTC into later Rocketdyne/Aerojet manifestations"
  searchResidual
  "targeted JPL/Caltech and patent-assignee search this round"
  "patent inventor/assignment genealogy remains source-backed, but no stronger 2025 JPL personnel or programme-custody carrier surfaced"
  "primary 2025 JPL/Caltech role plus exact Boeing/UTC/Rocketdyne/Aerojet same-object programme-custody crosswalk"
  false

carlGrillmairRound3 : Round3Progress
carlGrillmairRound3 = round3-progress
  "Carl J. Grillmair" us
  "institutional event identity and post-loss IPAC capability continuity"
  primaryPromotion
  "Caltech obituary 2026-02-21; IPAC People and Roles 2026-07-08"
  "Caltech directly records Grillmair's death on 2026-02-16 and IPAC later records broad 2026 staffing/leadership changes while mourning him; this supports institutional continuity after loss but does not identify a person-specific stellar-stream successor"
  "named post-loss stellar-stream/project/data custodian if one exists; otherwise retain as a capability-continuity control"
  false

michaelHicksRound3 : Round3Progress
michaelHicksRound3 = round3-progress
  "Michael David Hicks" us
  "exact 2022 JPL departure and unfinished-work/data transfer"
  controlStrengthening
  "University of Arizona LPL memorial; AAS DPS obituary"
  "institutional memorial again fixes JPL service to 1998-2022 and death on 2023-07-30; no evidence surfaced of an active JPL appointment at death, strengthening the pre-event departure control"
  "primary JPL separation/retirement carrier and any exact unfinished DART/NEAT/Dawn/DS1 data or project handover"
  false

neilMcCaslandRound3 : Round3Progress
neilMcCaslandRound3 = round3-progress
  "William Neil McCasland" us
  "dated DBE Consulting legal/entity role and 2025-2026 client/programme/tasking carrier"
  searchResidual
  "targeted public primary-source search this round"
  "no primary event-time DBE client, contract or programme object surfaced; secondary descriptions remain discovery coordinates only"
  "dated DBE entity/role record and exact 2025-2026 client/programme/tasking carrier"
  false

anthonyChavezRound3 : Round3Progress
anthonyChavezRound3 = round3-progress
  "Anthony Chavez" us
  "same-person weld between New Mexico missing-person carrier and LANL DARHT/Scorpius engineering carrier"
  primaryPromotion
  "New Mexico DPS missing-person record; LANL National Security Summer 2025 engineering profile"
  "two primary manifestations now independently pay the event identity and the engineering work identity, but no exact same-person bridge was located; source quality is no longer the blocker, identity welding is"
  "DOB/personnel/biographical same-person receipt linking the DPS missing person to the LANL engineering profile"
  false

jasonThomasRound3 : Round3Progress
jasonThomasRound3 = round3-progress
  "Jason R. Thomas" us
  "final Massachusetts medical-examiner carrier and exact lab/project/data succession"
  searchResidual
  "targeted Massachusetts/event and scientific-affiliation search this round"
  "no stronger final public ME object surfaced; mechanism science remains separated from event interpretation"
  "final public ME cause/manner if available, then named lab/project/data successor"
  false

amyEskridgeRound3 : Round3Progress
amyEskridgeRound3 = round3-progress
  "Amy Eskridge" us
  "Marshall POAMS-specific EDAA/NF-1676/STI same-object release carrier"
  searchResidual
  "targeted NASA/NTRS/Marshall POAMS/EDAA search this round"
  "no NASA-primary POAMS-specific release crosswalk surfaced; generic antigravity or community references remain non-promoting"
  "Amy-linked EDAA/NF-1676/STI object plus Institute derivative/transition same-object receipt"
  false

ningLiRound3 : Round3Progress
ningLiRound3 = round3-progress
  "Ning Li" us
  "recover actual DTIC/FBI/OIG response packages plus original FY2001 Army row/SOW/closeout"
  searchResidual
  "targeted DTIC/DoD/AC Gravity response-package search this round"
  "no public copy of the already logged DTIC package sent to requester, FBI 1499382-000 response or DoD OIG DODOIG-2022-001077 closure package surfaced; finite case identifiers remain the highest-value acquisition coordinates"
  "obtain response packages, original FY2001 DoD row, then Army SOW/payment/technical closeout and apparatus crosswalk"
  false

------------------------------------------------------------------------
-- Chinese scientific cohort (9)
------------------------------------------------------------------------

chenShumingRound3 : Round3Progress
chenShumingRound3 = round3-progress
  "Chen Shuming" china
  "primary event/death carrier and exact NUDT chip/project/publication identities"
  searchResidual
  "targeted NUDT/Chinese event search this round"
  "no higher-authority event carrier surfaced; the Galaxy/Feiteng work identity remains paid while event same-person/cause stays open"
  "primary event/death carrier plus exact project/publication objects attributable to the same Chen Shuming"
  false

fengYangheRound3 : Round3Progress
fengYangheRound3 = round3-progress
  "Feng Yanghe" china
  "primary NUDT/PLA event text and named War Skull succession"
  searchResidual
  "targeted NUDT primary-source search this round"
  "no primary NUDT/PLA event or successor surface displaced the existing bounded-secondary chronology"
  "primary event carrier, exact mission wording and named War Skull/team/project successor"
  false

zhouGuangyuanRound3 : Round3Progress
zhouGuangyuanRound3 = round3-progress
  "Zhou Guangyuan" china
  "post-loss centre leadership, project/IP custody and high-performance-polymer continuation"
  searchResidual
  "targeted DICP/CAS successor search this round"
  "the source-backed large-team/technology-transfer baseline remains strong, but no exact post-loss centre leader or IP/project custodian was located"
  "named post-loss high-performance-polymer centre leader plus project/patent/technology-transfer custody"
  false

liuDonghaoRound3 : Round3Progress
liuDonghaoRound3 = round3-progress
  "Liu Donghao" china
  "original company obituary, independent accident mechanism and organisational/project succession"
  searchResidual
  "targeted company/centre and event search this round"
  "no stronger original obituary or independent accident-mechanism carrier surfaced beyond the previously repaired event/work identity"
  "original centre/company event carrier plus first dated successor/DSMM project object"
  false

zhangXiaoxinRound3 : Round3Progress
zhangXiaoxinRound3 = round3-progress
  "Zhang Xiaoxin" china
  "post-loss Fengyun/space-weather programme custody versus stale authorship/committee surfaces"
  staleSurfaceDiscriminator
  "Advances in Space Research 2025 DOI 10.1016/j.asr.2025.02.010; current National Space Science Data Center committee page"
  "a 2025 FY-4B space-environment paper still lists Xiaoxin Zhang and a current NSSDC committee page still lists Zhang Xiaoxin after the 2024-12 death; these may reflect pre-death manuscript contribution or stale institutional metadata and do not by themselves pay post-loss active role or succession"
  "dated post-loss successor/project-custody object for NSMC space-weather/Fengyun work, plus manuscript submission/authorship chronology for 10.1016/j.asr.2025.02.010"
  false

zhangDaibingRound3 : Round3Progress
zhangDaibingRound3 = round3-progress
  "Zhang Daibing" china
  "primary obituary/company carrier and Yunzhihang/NUDT unmanned-system succession"
  boundedPromotion
  "SCMP 2025-01-08; secondary technical reporting on Yunzhihang firefighting-drone programme"
  "reporting further identifies Zhang as founder/chairman of Yunzhihang and ties the company to heavy-payload firefighting-drone technology, but a primary company succession/governance carrier remains missing"
  "primary Yunzhihang obituary/governance record and named successor/custodian for company and NUDT project portfolio"
  false

liMinyongRound3 : Round3Progress
liMinyongRound3 = round3-progress
  "Li Minyong" china
  "direct Hainan obituary manifestation and first post-loss project/patent/student succession"
  searchResidual
  "targeted Hainan University successor/project search this round"
  "no stronger direct successor/project object surfaced beyond the already repaired institutional obituary and work identity"
  "named post-loss project/patent/student/lab custodian for light-controlled drug discovery and bioactive visualisation"
  false

fangDainingRound3 : Round3Progress
fangDainingRound3 = round3-progress
  "Fang Daining" china
  "post-loss Institute of Advanced Structure Technology leadership and programme custody versus stale profile text"
  staleSurfaceDiscriminator
  "BIT Institute of Advanced Structure Technology current Fang Daining profile; 2026 institute publication surfaces"
  "BIT's live profile still states Fang was honorary director 'from 2015 up to now' after his 2026-02 death, while 2026 institute publications continue under other researchers; this is evidence that institutional profile persistence cannot be treated as active post-loss role continuity"
  "dated post-loss institute leadership/custody announcement and project-level handover for advanced-structure/metamaterial programmes"
  false

yanHongRound3 : Round3Progress
yanHongRound3 = round3-progress
  "Yan Hong" china
  "first dated post-loss NPU plasma/hypersonic project/team successor"
  searchResidual
  "targeted NPU successor/project search this round"
  "no exact post-loss lab/project successor surfaced beyond the already repaired NPU event/work identity and programme description"
  "named post-loss NPU flow-control/numerical-wind-tunnel project or team custodian"
  false

------------------------------------------------------------------------
-- Round-3 denominator and source-promotion firewalls.
------------------------------------------------------------------------

twentyScientistRound3Progress : List Round3Progress
twentyScientistRound3Progress =
  nunoLoureiroRound3 ∷ joshuaLeBlancRound3 ∷ frankMaiwaldRound3 ∷ monicaRezaRound3 ∷
  carlGrillmairRound3 ∷ michaelHicksRound3 ∷ neilMcCaslandRound3 ∷ anthonyChavezRound3 ∷
  jasonThomasRound3 ∷ amyEskridgeRound3 ∷ ningLiRound3 ∷
  chenShumingRound3 ∷ fengYangheRound3 ∷ zhouGuangyuanRound3 ∷ liuDonghaoRound3 ∷
  zhangXiaoxinRound3 ∷ zhangDaibingRound3 ∷ liMinyongRound3 ∷ fangDainingRound3 ∷
  yanHongRound3 ∷ []

round3ScientificCohortCount : Nat
round3ScientificCohortCount = 20

round3EveryScientistTouched : Bool
round3EveryScientistTouched = true

round3PromotionRequiresSourceReceipt : Bool
round3PromotionRequiresSourceReceipt = true

round3SearchResidualCreatesKnownAbsence : Bool
round3SearchResidualCreatesKnownAbsence = false

round3StaleSurfacePaysSuccession : Bool
round3StaleSurfacePaysSuccession = false

round3TechnicalAdjacencyCreatesCommonCause : Bool
round3TechnicalAdjacencyCreatesCommonCause = false
