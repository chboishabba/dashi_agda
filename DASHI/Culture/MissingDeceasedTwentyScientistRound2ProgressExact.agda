module DASHI.Culture.MissingDeceasedTwentyScientistRound2ProgressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SECOND TWENTY-SCIENTIST ROUND
--
-- Every retained scientist is touched again.  A row records the freshest
-- source-backed delta or, when no stronger source surfaced, a bounded search
-- residual.  Search effort and technical adjacency do not pay the next leaf.
------------------------------------------------------------------------

data Round2Side : Set where us china : Round2Side

data Round2ResultKind : Set where
  primaryPromotion boundedPromotion searchResidual controlStrengthening : Round2ResultKind

record Round2Progress : Set where
  constructor round2-progress
  field
    person : String
    side : Round2Side
    searchTarget : String
    resultKind : Round2ResultKind
    sourceReference : String
    freshDelta : String
    nextExactLeaf : String
    leafPaid : Bool

open Round2Progress public

------------------------------------------------------------------------
-- United States scientific cohort (11)
------------------------------------------------------------------------

nunoLoureiroRound2 : Round2Progress
nunoLoureiroRound2 = round2-progress
  "Nuno F. G. Loureiro" us
  "exact post-loss Viriato/KREHM repository, grant, student and simulation-state custody"
  controlStrengthening
  "MIT News 2025-12-16; MIT PSFC memorial/support surfaces"
  "MIT primary memorial material identifies named students, collaborators and institutional continuation; it strengthens broad pedagogical/community continuity but still does not identify exact Viriato/KREHM repository, grant or simulation-state custody"
  "named same-work repository/grant/advisor/simulation-state transfer for Viriato/KREHM"
  false

joshuaLeBlancRound2 : Round2Progress
joshuaLeBlancRound2 = round2-progress
  "Joshua Kyle LeBlanc" us
  "post-loss FSP/SNP I&C role snapshot versus actual successor/handover"
  primaryPromotion
  "NASA NTRS 20250008475; acquired 2025-08-16 for FSP Technology Maturation webinar 2025-08-26"
  "the NASA webinar deck still lists Joshua LeBlanc as NASA SNP I&C TechMat Team Lead after his 2025-07-22 death; this pays a post-loss stale/frozen role manifestation, not a successor or handover"
  "first dated successor/roster revision plus qualification, calibration and failure-data custody transfer"
  false

frankMaiwaldRound2 : Round2Progress
frankMaiwaldRound2 = round2-progress
  "Frank W. Maiwald" us
  "SURP PI transition and exact spectra/calibration/data custody"
  primaryPromotion
  "JPL SURP 2023 index and SP23012p; JPL SURP 2024/2025 manifestations"
  "JPL source surfaces continue to support 2023 Maiwald PI -> 2024/2025 Nemchick PI project-manifestation succession; no primary object yet pays raw/reduced spectra, calibration or notebook custody"
  "administrative PI-change date and exact dataset/calibration/notebook/publication manifestation crosswalk"
  false

monicaRezaRound2 : Round2Progress
monicaRezaRound2 = round2-progress
  "Monica Jacinto / Monica Reza" us
  "patent custody chain and event-time JPL role"
  primaryPromotion
  "Google Patents US20030053926A1 and US20040208777A1"
  "the patent genealogy independently confirms Monica Jacinto and Dallis Hardwick as inventors; the 2004 continuation records assignment to Boeing and later United Technologies, sharpening material-IP custody without paying Reza's 2025 JPL event-time role"
  "primary 2025 JPL/Caltech personnel role plus programme/process-window successor; reconcile patent assignee genealogy with later Rocketdyne ownership"
  false

carlGrillmairRound2 : Round2Progress
carlGrillmairRound2 = round2-progress
  "Carl J. Grillmair" us
  "post-event manuscript/repository continuity control"
  controlStrengthening
  "CaltechAUTHORS published/accepted stellar-stream records including 10.3847/1538-4357/aa8872 and M2 tidal-tail work"
  "Caltech repository continues to expose a substantial published/accepted stream corpus with stable files and identifiers; no source-backed technical-disruption signal surfaced this round"
  "date any manuscript/data/repository changes around the event only if primary metadata exists; otherwise retain as continuity control"
  false

michaelHicksRound2 : Round2Progress
michaelHicksRound2 = round2-progress
  "Michael David Hicks" us
  "JPL departure and unfinished-work transfer"
  primaryPromotion
  "AAS Division for Planetary Sciences obituary; University of Arizona LPL memorial; JPL Family News October 2023"
  "three institutional/professional memorial surfaces independently state Hicks worked at JPL from 1998 until 2022 and died 2023-07-30; this strengthens the pre-death departure boundary and weakens any assumption that his 2023 death directly removed an active JPL role"
  "exact 2022 JPL departure/retirement/separation carrier and any unfinished DART/NEAT/Dawn/DS1 data or project handover"
  false

neilMcCaslandRound2 : Round2Progress
neilMcCaslandRound2 = round2-progress
  "William Neil McCasland" us
  "event-time DBE Consulting/client/programme status"
  searchResidual
  "targeted web search; secondary Sentinel/biographical surfaces only"
  "search surfaced secondary assertions about DBE Consulting and multiple boards but no primary 2025-2026 client, contract or tasking object; these claims remain discovery coordinates only"
  "dated DBE legal/entity record and exact 2025-2026 client/programme/tasking carrier"
  false

anthonyChavezRound2 : Round2Progress
anthonyChavezRound2 = round2-progress
  "Anthony Chavez" us
  "same-person weld between missing-person identity and LANL DARHT/Scorpius profile"
  primaryPromotion
  "LANL National Security Summer 2025 engineering profile"
  "LANL primary material again pays the engineering carrier: Los Alamos since 1989, mechanical-engineering degree, more than 25 years at DARHT and completed Scorpius design work; it still does not by itself weld to the missing-person identity"
  "primary identity receipt linking the missing Anthony Chavez to the LANL profile; keep Mark Anthony Chavez publication carrier separate"
  false

jasonThomasRound2 : Round2Progress
jasonThomasRound2 = round2-progress
  "Jason R. Thomas" us
  "final medical-examiner event carrier and exact research succession"
  searchResidual
  "targeted web search for final Massachusetts ME + STING/ferritinophagy identity"
  "no stronger final medical-examiner source surfaced this round; existing scientific mechanism owners remain separate from the preliminary event/no-foul-play boundary"
  "final public ME cause/manner if available, then exact lab/project successor and data custody"
  false

amyEskridgeRound2 : Round2Progress
amyEskridgeRound2 = round2-progress
  "Amy Eskridge" us
  "Marshall POAMS EDAA/STI same-object release and Institute derivative lineage"
  searchResidual
  "targeted NASA/POAMS/EDAA web search; only community retellings surfaced"
  "no NASA primary POAMS-specific EDAA/STI crosswalk surfaced; community claims about a blocked 2020 release remain non-promoting"
  "Amy-linked Marshall EDAA/NF-1676/STI carrier, exact reviewed object and Institute derivative identity"
  false

ningLiRound2 : Round2Progress
ningLiRound2 = round2-progress
  "Ning Li" us
  "Army/AC Gravity source genealogy, response packages and identifier/accounting collision"
  primaryPromotion
  "DTIC FOIA log; FBI FOIA log 1499382-000; DoD OIG DODOIG-2022-001077; Texas State Auditor reports 06-325/07-316"
  "this round adds finite government-response acquisition keys and preserves the FY2005/FY2006 DAAH01-01-9-R001 recurrence; request logs do not reveal response contents and the Texas recurrence does not pay a Lockheed-AC Gravity relationship"
  "recover DTIC package sent to requester, FBI/OIG response packages, original FY2001 DoD row, then Army SOW/payment/technical closeout"
  false

------------------------------------------------------------------------
-- Chinese scientific cohort (9)
------------------------------------------------------------------------

chenShumingRound2 : Round2Progress
chenShumingRound2 = round2-progress
  "Chen Shuming" china
  "primary event/death identity and exact NUDT chip project/publication objects"
  searchResidual
  "targeted Chinese/English web search around NUDT Chen Shuming event identity"
  "no higher-authority event carrier surfaced in this round; retain the paid NUDT Galaxy/Feiteng work carrier without promoting death cause or same-person event identity"
  "primary event/death carrier plus exact chip/project/publication objects attributable to the same Chen Shuming"
  false

fengYangheRound2 : Round2Progress
fengYangheRound2 = round2-progress
  "Feng Yanghe" china
  "primary NUDT/PLA event carrier and post-loss War Skull succession"
  boundedPromotion
  "SCMP event reporting plus previously paid NUDT War Skull/press sources"
  "the event chronology remains bounded-secondary: death 2023-07-01 and military funeral/major-task reporting; no primary NUDT/PLA event text surfaced in this round"
  "primary institutional event carrier, exact mission wording, then named War Skull/team/project successor"
  false

zhouGuangyuanRound2 : Round2Progress
zhouGuangyuanRound2 = round2-progress
  "Zhou Guangyuan" china
  "event identity plus centre/team and technology-transfer succession"
  primaryPromotion
  "Chinese Academy of Sciences/Dalian Institute of Chemical Physics 2024 memorial feature"
  "CAS/DICP source-backed memorial fixes death on 2023-12-16 and describes his 2019 move to DICP, creation of the high-performance polymer-materials centre group in 2022, growth from roughly a dozen followers to more than one hundred members, and enterprise technology-transfer collaboration"
  "exact post-loss centre leadership, project/IP custody and continuation of the polyimide-aerogel/application programmes"
  false

liuDonghaoRound2 : Round2Progress
liuDonghaoRound2 = round2-progress
  "Liu Donghao" china
  "independent accident mechanism and organisational/project succession"
  boundedPromotion
  "company-obituary reporting reproduced by Chinese finance/news outlets"
  "reporting consistently attributes a 2024-03-05 accidental death to the Big Data Security Engineering Research Center company obituary; mechanism remains unspecified and no independent forensic carrier surfaced"
  "original company obituary, independent event mechanism if public, and first dated successor/centre project object"
  false

zhangXiaoxinRound2 : Round2Progress
zhangXiaoxinRound2 = round2-progress
  "Zhang Xiaoxin" china
  "independent traffic-event record and Fengyun/space-weather succession"
  searchResidual
  "targeted Chinese institutional/news search"
  "no stronger primary event or project-successor object surfaced beyond the already repaired NSMC obituary/work identity; residual remains programme succession rather than identity discovery"
  "independent traffic-event carrier plus first exact post-loss Fengyun/space-weather programme successor/custody object"
  false

zhangDaibingRound2 : Round2Progress
zhangDaibingRound2 = round2-progress
  "Zhang Daibing" china
  "event identity and post-NUDT company/project custody"
  boundedPromotion
  "South China Morning Post 2025-01-08 obituary reporting"
  "bounded reporting fixes death on 2025-01-03, age 47, and identifies him as chairman of a drone start-up and former deputy director of NUDT's Unmanned Systems Research Institute; obituary did not state cause"
  "primary obituary/company carrier and named successor/custodian for the start-up and NUDT unmanned-system project portfolio"
  false

liMinyongRound2 : Round2Progress
liMinyongRound2 = round2-progress
  "Li Minyong" china
  "primary event identity and research/project succession"
  primaryPromotion
  "Hainan University School of Pharmaceutical Sciences obituary as reproduced by Beijing Daily 2025-11-18"
  "institutional obituary states Li died 2025-11-16 in Guangzhou after sudden illness despite rescue efforts, while identifying him as Hainan University professor/deputy dean and his visualization/light-controlled drug-research programme"
  "direct Hainan obituary manifestation plus first post-loss project/patent/student succession object"
  false

fangDainingRound2 : Round2Progress
fangDainingRound2 = round2-progress
  "Fang Daining" china
  "primary event identity plus advanced-materials/metamaterial programme succession"
  primaryPromotion
  "Chinese Academy of Sciences memorial; BIT faculty/research profile; DOI 10.1002/advs.202102662; DOI 10.1016/j.jmps.2025.106144"
  "CAS memorial states Fang died of illness on 2026-02-27 and independently characterises his advanced-materials/structural-mechanics work; current publication surfaces show active-mechanical-metamaterial work continuing into 2025, providing a strong pre-event continuity baseline"
  "first dated post-loss BIT/Peking advanced-structure project/team leadership and custody object; keep metamaterial science separate from provenance claims"
  false

yanHongRound2 : Round2Progress
yanHongRound2 = round2-progress
  "Yan Hong" china
  "primary NPU event/work carrier and successor/project continuity"
  primaryPromotion
  "NPU School of Power and Energy obituary as reproduced by ScienceNet/The Paper 2026-03-26"
  "institutional-source obituary fixes death after illness on 2026-03-24 17:19 at Jiangsu Provincial People's Hospital and identifies her supersonic/hypersonic, plasma-flow-control and CFD programme, including national project leadership"
  "direct NPU manifestation plus first dated post-loss lab/project successor for flow-control and numerical-wind-tunnel work"
  false

------------------------------------------------------------------------
-- Round-2 denominator and firewalls.
------------------------------------------------------------------------

twentyScientistRound2Progress : List Round2Progress
twentyScientistRound2Progress =
  nunoLoureiroRound2 ∷ joshuaLeBlancRound2 ∷ frankMaiwaldRound2 ∷ monicaRezaRound2 ∷
  carlGrillmairRound2 ∷ michaelHicksRound2 ∷ neilMcCaslandRound2 ∷ anthonyChavezRound2 ∷
  jasonThomasRound2 ∷ amyEskridgeRound2 ∷ ningLiRound2 ∷
  chenShumingRound2 ∷ fengYangheRound2 ∷ zhouGuangyuanRound2 ∷ liuDonghaoRound2 ∷
  zhangXiaoxinRound2 ∷ zhangDaibingRound2 ∷ liMinyongRound2 ∷ fangDainingRound2 ∷
  yanHongRound2 ∷ []

round2ScientificCohortCount : Nat
round2ScientificCohortCount = 20

round2EveryScientistTouched : Bool
round2EveryScientistTouched = true

round2PromotionRequiresSourceReceipt : Bool
round2PromotionRequiresSourceReceipt = true

round2SearchResidualCreatesKnownAbsence : Bool
round2SearchResidualCreatesKnownAbsence = false

round2TechnicalAdjacencyCreatesCommonCause : Bool
round2TechnicalAdjacencyCreatesCommonCause = false
