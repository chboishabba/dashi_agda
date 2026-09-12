module DASHI.Culture.MissingDeceasedTwentyScientistRound4ProgressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- FOURTH TWENTY-SCIENTIST ROUND
--
-- This round targets capability-state succession rather than merely asking
-- whether an institution or webpage survives.  A current team/dean/convener,
-- when source-exact, may pay a bounded succession coordinate.  A stale profile,
-- posthumous paper or institutional continuation cannot by itself pay transfer
-- of the deceased person's code, data, IP, calibration state or project role.
------------------------------------------------------------------------

data Round4Side : Set where us china : Round4Side

data Round4ResultKind : Set where
  primaryPromotion boundedPromotion searchResidual controlStrengthening
  staleSurfaceDiscriminator capabilitySuccessionPromotion redundancyBaseline : Round4ResultKind

record Round4Progress : Set where
  constructor round4-progress
  field
    person : String
    side : Round4Side
    searchTarget : String
    resultKind : Round4ResultKind
    sourceReference : String
    freshDelta : String
    nextExactLeaf : String
    leafPaid : Bool

open Round4Progress public

------------------------------------------------------------------------
-- United States scientific cohort (11)
------------------------------------------------------------------------

nunoLoureiroRound4 : Round4Progress
nunoLoureiroRound4 = round4-progress
  "Nuno F. G. Loureiro" us
  "same-work Viriato/KREHM repository, grant and simulation-state transfer"
  controlStrengthening
  "MIT News/PSFC memorial and current PSFC support surfaces"
  "MIT continues to document broad student and institutional continuity and a memorial fund supporting PSFC/NSE graduate students; no exact Viriato/KREHM repository, grant or simulation-state successor surfaced this round"
  "named same-work code repository maintainer, grant transfer, student-advisor reassignment or simulation-state custodian"
  false

joshuaLeBlancRound4 : Round4Progress
joshuaLeBlancRound4 = round4-progress
  "Joshua Kyle LeBlanc" us
  "FSP/SNP I&C capability continuation versus person-specific TechMat succession"
  controlStrengthening
  "NASA Fission Surface Power project page and TechPort project 105671, current 2026"
  "NASA's FSP project is explicitly active in 2026 and continues design, system integration and qualification work after LeBlanc's death; this pays programme-level capability continuity but still does not identify the successor to LeBlanc's SNP I&C TechMat role"
  "first dated TechMat roster revision plus named successor/handover and calibration/failure/qualification-data custody"
  false

frankMaiwaldRound4 : Round4Progress
frankMaiwaldRound4 = round4-progress
  "Frank W. Maiwald" us
  "action-spectroscopy data/calibration custody and exact project handover"
  controlStrengthening
  "JPL Molecular Spectroscopy current team page; JPL Deacon Nemchick profile"
  "JPL's current molecular-spectroscopy capability includes Deacon Nemchick and a continuing spectroscopy team, strengthening laboratory-capability continuity; it does not pay custody of Maiwald's SURP spectra, calibration files, notebooks or project-specific handover"
  "project-specific SURP handover record and raw/reduced spectra, calibration, notebook and publication-manifestation custody"
  false

monicaRezaRound4 : Round4Progress
monicaRezaRound4 = round4-progress
  "Monica Jacinto / Monica Reza" us
  "patent-assignment same-object chain into Rocketdyne/Aerojet plus 2025 JPL role"
  primaryPromotion
  "Google Patents US20040208777A1"
  "the primary patent history pays assignment of Jacinto/Hardwick's alloy application to Boeing on 2004-01-30 and Boeing-to-United-Technologies assignments in 2006; the current patent surface identifies Aerojet Rocketdyne of DE Inc in the assignee lineage, sharpening corporate custody without paying a 2025 JPL role or proving one continuous programme"
  "assignment-instrument chain from UTC to Rocketdyne/Aerojet plus primary 2025 JPL/Caltech role and process-window successor"
  false

carlGrillmairRound4 : Round4Progress
carlGrillmairRound4 = round4-progress
  "Carl J. Grillmair" us
  "stellar-stream capability/data succession inside IPAC"
  controlStrengthening
  "Caltech/IPAC memorial and current IPAC institutional surfaces"
  "IPAC directly records Grillmair's stellar-stream and exoplanet work and continues as an operating science/data centre after his death; no named stellar-stream data or manuscript custodian was located this round"
  "named successor/custodian for Grillmair stream catalogs, matched-filter products, orbit fits or unfinished manuscripts"
  false

michaelHicksRound4 : Round4Progress
michaelHicksRound4 = round4-progress
  "Michael David Hicks" us
  "exact 2022 JPL separation and unfinished data/project transfer"
  controlStrengthening
  "University of Arizona LPL memorial and AAS DPS memorial"
  "institutional memorials continue to bound Hicks's JPL service to 1998-2022, before his 2023 death; no exact separation document or unfinished-project/data handover surfaced"
  "primary 2022 JPL separation/retirement carrier and any unfinished DART/NEAT/Dawn/DS1 data or project handover"
  false

neilMcCaslandRound4 : Round4Progress
neilMcCaslandRound4 = round4-progress
  "William Neil McCasland" us
  "dated DBE Consulting legal/entity role and 2025-2026 tasking"
  searchResidual
  "targeted primary-source search this round"
  "no primary DBE Consulting client, contract, board or tasking object dated 2025-2026 surfaced; secondary biography claims remain discovery-only"
  "dated legal/entity DBE role plus exact 2025-2026 client/programme/tasking carrier"
  false

anthonyChavezRound4 : Round4Progress
anthonyChavezRound4 = round4-progress
  "Anthony Chavez" us
  "same-person weld between NM missing-person identity and LANL engineering carrier"
  primaryPromotion
  "New Mexico DPS M99969; Los Alamos County/LAPD May 2025 releases; LANL Summer 2025 engineering profile"
  "NM DPS and Los Alamos County independently pay the missing-person identity/location and search chronology, while LANL independently pays the DARHT/Scorpius engineering carrier; the exact cross-carrier same-person weld is still unpaid"
  "birth/age/employment or police/LANL identity receipt directly welding the missing Anthony Chavez to the LANL engineering profile"
  false

jasonThomasRound4 : Round4Progress
jasonThomasRound4 = round4-progress
  "Jason R. Thomas" us
  "final medical-examiner cause/manner and lab/project succession"
  boundedPromotion
  "Edward V. Sullivan Funeral Home obituary / obituary distribution surfaces"
  "a funeral-home obituary now fixes death on 2026-03-17 after Thomas had been missing since 2025-12-12; it is an event chronology carrier, not a medical-examiner cause/manner determination"
  "final public Massachusetts ME cause/manner if available plus exact STING/ferritinophagy lab/project/data successor"
  false

amyEskridgeRound4 : Round4Progress
amyEskridgeRound4 = round4-progress
  "Amy Eskridge" us
  "POAMS-specific NF-1676/EDAA/STRIVES same-object release carrier"
  controlStrengthening
  "NASA STI policy NPR 2200.2C/2D; current STI STRIVES/NF-1676 guidance; NTRS 20205010911"
  "NASA policy independently requires technical review and NF-1676 dissemination review for published STI and current guidance routes NASA authors through STRIVES; this strengthens the expected metadata/custody path for POAMS but still does not locate Amy's claimed 2020 reviewed object or a POAMS-specific EDAA identifier"
  "Amy-linked POAMS NF-1676/EDAA/STRIVES record, attached STI version and same-object correspondence"
  false

ningLiRound4 : Round4Progress
ningLiRound4 = round4-progress
  "Ning Li" us
  "DTIC/FBI/OIG response packages and original FY2001 Army agreement row"
  searchResidual
  "targeted DTIC/AC Gravity/DAAH01-01-9-R001 search this round"
  "no new primary response package or original FY2001 row surfaced beyond the already formalised request-log and Texas-accounting coordinates"
  "recover DTIC package sent to requester, FBI/OIG response packages, original FY2001 DoD row, Army SOW and technical closeout"
  false

------------------------------------------------------------------------
-- Chinese scientific cohort (9)
------------------------------------------------------------------------

chenShumingRound4 : Round4Progress
chenShumingRound4 = round4-progress
  "Chen Shuming" china
  "event identity plus capability redundancy within Galaxy/Feiteng team"
  redundancyBaseline
  "NUDT 2026-01-29 Galaxy/Feiteng team history"
  "NUDT's current institutional history places Chen Shuming among middle-generation technical backbones while naming older technical gatekeepers and younger-generation verification/layout engineers; this pays a multi-generation team baseline, not Chen's event identity or individual project custody"
  "primary event/death carrier plus exact Chen-attributable project/publication objects and any post-loss role redistribution"
  false

fengYangheRound4 : Round4Progress
fengYangheRound4 = round4-progress
  "Feng Yanghe" china
  "post-loss War Skull technical/team succession"
  redundancyBaseline
  "NUDT War Skull II institutional article"
  "NUDT's primary War Skull II article names team members Zhang Longfei and Zhang Yulong and professor Huang Jincai, and explicitly describes collective iterative algorithm/code development; this pays pre-loss team redundancy but not a post-loss successor to Feng or custody of his exact modules"
  "post-2023 NUDT War Skull/decision-agent project object naming technical lead, code custodian or successor"
  false

zhouGuangyuanRound4 : Round4Progress
zhouGuangyuanRound4 = round4-progress
  "Zhou Guangyuan" china
  "named post-loss DNL2200 centre leadership and programme/IP custody"
  capabilitySuccessionPromotion
  "DICP Energy Materials Research Division current overview, DNL2200 High-Performance Polymer Materials Research Center"
  "DICP's current primary page now names Hu Yanming as temporary convener of DNL2200 and separately lists Hu Yanming and Wang Rui as group leaders; this is a genuine post-loss leadership-state receipt for the centre created by Zhou, while exact IP/project/enterprise-transfer custody remains to be mapped"
  "date Hu Yanming's appointment and map specific polyimide-aerogel, engineering-plastics, patent and enterprise-transfer projects into the successor groups"
  false

liuDonghaoRound4 : Round4Progress
liuDonghaoRound4 = round4-progress
  "Liu Donghao" china
  "centre/company governance succession after 2024-03-05"
  boundedPromotion
  "Big Data Security Engineering Research Center (Guizhou) live governance page"
  "the live centre page contains a historical governance block naming Liu Donghao as secretary-general/CEO and another governance block naming Liao Fang as secretary-general/CEO; without dated section labels this is a strong succession lead but not yet an exact transition-date receipt"
  "dated board/company filing or centre announcement establishing Liu-to-Liao governance transition and first post-loss DSMM/project custody"
  false

zhangXiaoxinRound4 : Round4Progress
zhangXiaoxinRound4 = round4-progress
  "Zhang Xiaoxin" china
  "true space-weather successor versus stale committee/publication surfaces"
  staleSurfaceDiscriminator
  "NSMC Space Weather Committee and SAT/TC347/SC3 current pages"
  "current NSMC committee and standardisation pages still list Zhang Xiaoxin as deputy chair after his death; this strengthens the stale-governance-surface discriminator and cannot pay active post-loss role continuity"
  "dated committee reconstitution or named NSMC/Fengyun space-weather project successor plus publication-submission chronology"
  false

zhangDaibingRound4 : Round4Progress
zhangDaibingRound4 = round4-progress
  "Zhang Daibing" china
  "Yunzhihang corporate successor and unmanned-system project custody"
  searchResidual
  "targeted Yunzhihang/NUDT successor search this round"
  "secondary obituary reporting still identifies Zhang as founder/chairman and former NUDT institute deputy director, but no primary company governance or successor carrier surfaced"
  "primary company filing/announcement naming new chair or project custodian plus NUDT unmanned-system successor"
  false

liMinyongRound4 : Round4Progress
liMinyongRound4 = round4-progress
  "Li Minyong" china
  "post-loss Hainan lab/project/student succession"
  searchResidual
  "targeted Hainan University 2026 project/lab search this round"
  "no named post-loss custodian for Li's light-controlled drug discovery or bioactive visualisation programme surfaced beyond the already repaired event/work identity"
  "named post-loss lab/project/patent/student custodian and dated Hainan organisational transition"
  false

fangDainingRound4 : Round4Progress
fangDainingRound4 = round4-progress
  "Fang Daining" china
  "Institute of Advanced Structure Technology leadership topology around loss"
  capabilitySuccessionPromotion
  "BIT Institute of Advanced Structure Technology 2026-01-12 planning meeting; CAS obituary; current institute homepage"
  "before Fang's death, BIT already identified Yang Yazheng as institute party secretary/dean and Fang as chief scientist; therefore executive institute leadership was distributed before the event. The institute remains active in 2026, but exact project/IP/metamaterial custody still requires project-level receipts"
  "post-loss institute announcement and project-level handover for Fang-led advanced-materials, metamaterial and extreme-environment programmes"
  false

yanHongRound4 : Round4Progress
yanHongRound4 = round4-progress
  "Yan Hong" china
  "post-loss NPU plasma/hypersonic project successor versus stale governance surfaces"
  staleSurfaceDiscriminator
  "NPU School of Power and Energy academic committee page dated 2024-01-18; current 2026 school pages"
  "the still-live academic-committee page lists Yan Hong but is explicitly dated 2024-01-18, before her 2026 death; its continued availability cannot be treated as current role state or succession. Current school activity shows institutional continuity only"
  "dated post-loss NPU committee/project roster naming successor for plasma-flow-control, inlet or numerical-wind-tunnel work"
  false

------------------------------------------------------------------------
-- Round-4 denominator and firewalls.
------------------------------------------------------------------------

twentyScientistRound4Progress : List Round4Progress
twentyScientistRound4Progress =
  nunoLoureiroRound4 ∷ joshuaLeBlancRound4 ∷ frankMaiwaldRound4 ∷ monicaRezaRound4 ∷
  carlGrillmairRound4 ∷ michaelHicksRound4 ∷ neilMcCaslandRound4 ∷ anthonyChavezRound4 ∷
  jasonThomasRound4 ∷ amyEskridgeRound4 ∷ ningLiRound4 ∷
  chenShumingRound4 ∷ fengYangheRound4 ∷ zhouGuangyuanRound4 ∷ liuDonghaoRound4 ∷
  zhangXiaoxinRound4 ∷ zhangDaibingRound4 ∷ liMinyongRound4 ∷ fangDainingRound4 ∷
  yanHongRound4 ∷ []

round4ScientificCohortCount : Nat
round4ScientificCohortCount = 20

round4EveryScientistTouched : Bool
round4EveryScientistTouched = true

round4PromotionRequiresSourceReceipt : Bool
round4PromotionRequiresSourceReceipt = true

round4SearchResidualCreatesKnownAbsence : Bool
round4SearchResidualCreatesKnownAbsence = false

round4StaleSurfacePaysSuccession : Bool
round4StaleSurfacePaysSuccession = false

round4InstitutionContinuityPaysCapabilityTransfer : Bool
round4InstitutionContinuityPaysCapabilityTransfer = false

round4NamedLeaderPaysProjectIPCustody : Bool
round4NamedLeaderPaysProjectIPCustody = false

round4TechnicalAdjacencyCreatesCommonCause : Bool
round4TechnicalAdjacencyCreatesCommonCause = false
