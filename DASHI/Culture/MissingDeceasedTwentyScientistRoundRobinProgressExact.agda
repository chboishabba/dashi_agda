module DASHI.Culture.MissingDeceasedTwentyScientistRoundRobinProgressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- TWENTY-SCIENTIST ROUND-ROBIN INVESTIGATIVE PROGRESS LEDGER
--
-- User-level invariant: every investigation round must touch every retained
-- scientist in the scientific denominator, not only the current highest-alpha
-- person.  This ledger fixes the present scientific cohort at 11 U.S. + 9
-- Chinese scientists.  Non-scientist/support rows remain in the parallel
-- role/event audit and are not silently promoted into this denominator.
--
-- A round target is a proof-search/acquisition obligation, not payment of the
-- leaf.  Negative/no-better-source searches are retained as search residuals.
------------------------------------------------------------------------

data CohortSide : Set where
  unitedStates china : CohortSide

record ScientistRoundProgress : Set where
  constructor scientist-round-progress
  field
    person : String
    cohortSide : CohortSide
    currentOwnedKernel : String
    roundSearchCoordinate : String
    roundDelta : String
    nextExactLeaf : String
    promotedThisRound : Bool
    retainedInPareto : Bool

open ScientistRoundProgress public

------------------------------------------------------------------------
-- U.S. scientific cohort (11)
------------------------------------------------------------------------

nunoLoureiroRound : ScientistRoundProgress
nunoLoureiroRound = scientist-round-progress
  "Nuno F. G. Loureiro"
  unitedStates
  "Viriato/KREHM/Hermite/plasmoid/turbulence science plus PSFC leadership surface"
  "MIT PSFC memorial/student/continuity surfaces; repository/grant/student succession"
  "current-round MIT primary search found memorial material identifying multiple students, group leaders and initiatives explicitly continuing after Loureiro; this supports pedagogical/community continuity but not exact Viriato/KREHM repository, grant or simulation-state custody"
  "named post-loss advisor/grant/repository/simulation-state transfer for the exact Viriato/KREHM work"
  false true

joshuaLeBlancRound : ScientistRoundProgress
joshuaLeBlancRound = scientist-round-progress
  "Joshua Kyle LeBlanc"
  unitedStates
  "Fission Surface Power instrumentation-and-controls maturation"
  "NASA FSP/SNP TechMat roster, qualification/failure/calibration handover"
  "targeted primary-source search was rerun this round; no stronger exact post-loss roster carrier displaced the existing residual"
  "first exact post-loss SNP I&C TechMat roster plus same-carrier qualification/failure/calibration handover"
  false true

frankMaiwaldRound : ScientistRoundProgress
frankMaiwaldRound = scientist-round-progress
  "Frank W. Maiwald"
  unitedStates
  "action spectroscopy and planetary quadrupole-ion-trap mass spectrometry; 2023->2025 SURP PI succession surface"
  "JPL SURP manifestations, raw/reduced spectra, calibration/notebook/data custody"
  "current round preserves the paid 2023 Maiwald -> 2024/2025 Nemchick project-manifestation succession; no source upgrades raw-data custody"
  "administrative PI-change date plus dataset/calibration/notebook custody and exact spectra/publication manifestation crosswalk"
  false true

monicaRezaRound : ScientistRoundProgress
monicaRezaRound = scientist-round-progress
  "Monica Jacinto / Monica Reza"
  unitedStates
  "oxygen-rich burn-resistant high-strength Ni-alloy, gamma/gamma-prime microstructure and process chain"
  "primary JPL/Caltech event-time role, patent/programme provenance, process-window succession"
  "targeted JPL/Caltech search was rerun; no stronger event-time personnel carrier surfaced, so the material-science kernel remains paid while person-specific 2025 role/process custody remains open"
  "primary event-time JPL/Caltech Materials Processing role record and exact programme/process-window successor"
  false true

carlGrillmairRound : ScientistRoundProgress
carlGrillmairRound = scientist-round-progress
  "Carl J. Grillmair"
  unitedStates
  "stellar-stream matched-filter/orbit work"
  "CaltechAUTHORS manuscript/repository continuity as a control"
  "current-round Caltech search reconfirmed source-backed stellar-stream publications; no new same-work disruption signal surfaced, so Grillmair remains a continuity/control lane rather than a common-cause promotion"
  "post-event manuscript/repository continuation only where source-exact; preserve charged local-crime event fibre separately"
  false true

michaelHicksRound : ScientistRoundProgress
michaelHicksRound = scientist-round-progress
  "Michael David Hicks"
  unitedStates
  "comet/asteroid spectrophotometry and small-body photometry"
  "JPL departure timing and unfinished-work transfer"
  "current-round JPL search reconfirmed Hicks participation in optical asteroid lightcurve work but did not pay the 2022 departure/unfinished-work transfer residual"
  "primary 2022 JPL departure and exact unfinished-work/data/project transfer carrier"
  false true

neilMcCaslandRound : ScientistRoundProgress
neilMcCaslandRound = scientist-round-progress
  "William Neil McCasland"
  unitedStates
  "fault-tolerant flexible-structure control plus AFRL/space-programme leadership history"
  "DBE Consulting event-time status and 2025-2026 client/programme carrier"
  "targeted event-time programme search was rerun; no primary 2025-2026 DBE client/programme object surfaced, so stale historical role prose remains non-promoting"
  "dated DBE legal/entity role plus exact 2025-2026 client/programme/tasking carrier"
  false true

anthonyChavezRound : ScientistRoundProgress
anthonyChavezRound = scientist-round-progress
  "Anthony Chavez"
  unitedStates
  "split carriers: missing-person identity versus LANL DARHT/Scorpius engineering identity"
  "same-person identity weld before technical inheritance"
  "current-round LANL primary search reconfirmed the Summer-2025 Anthony Chavez engineering profile: Los Alamos since 1989, mechanical-engineering degree, more than 25 years at DARHT and completed Scorpius design work; this strengthens the work carrier but does not weld it to the missing-person identity"
  "primary same-person receipt linking the missing Anthony Chavez to the LANL Summer-2025 profile; publication identity remains separately gated"
  true true

jasonThomasRound : ScientistRoundProgress
jasonThomasRound = scientist-round-progress
  "Jason R. Thomas"
  unitedStates
  "STING signalling and VPS34/NCOA4 ferritinophagy mechanism work"
  "final Massachusetts medical-examiner cause/manner and exact research succession"
  "targeted event-source search was rerun; no stronger final ME carrier displaced the existing preliminary no-foul-play boundary"
  "final public ME identity/cause/manner if available, then exact lab/project succession without inferring cause from science"
  false true

amyEskridgeRound : ScientistRoundProgress
amyEskridgeRound = scientist-round-progress
  "Amy Eskridge"
  unitedStates
  "engineered-gravity mechanism discrimination, Institute succession and POAMS release archaeology"
  "Marshall EDAA/NF-1676/STI same-object release/transition receipt"
  "current-round NASA-targeted search did not recover the missing POAMS-specific EDAA/STI crosswalk; the residual stays exact rather than being filled by generic NASA antigravity material"
  "Amy-linked same-object Marshall EDAA/STI carrier and Institute derivative/transition identity"
  false true

ningLiRound : ScientistRoundProgress
ningLiRound = scientist-round-progress
  "Ning Li"
  unitedStates
  "Li/Torr theory, 1997 static YBCO constraint, 1998 rotating-field constraint and NASA NCC8-124 programme"
  "DAAH01-01-9-R001 Army row/SOW/closeout plus FY2005/FY2006 Texas identifier recurrence"
  "current round added a two-year primary Texas audit recurrence for the identifier and a FOIA procedural correction: recurrence weakens a one-off OCR hypothesis, while case 23-F-0043 was administratively closed rather than a substantive no-records finding"
  "inspect original FY2001 DoD row and full Texas row/recipient semantics, then Army SOW/payment/technical closeout and apparatus comparison"
  true true

------------------------------------------------------------------------
-- Chinese scientific cohort (9)
------------------------------------------------------------------------

chenShumingRound : ScientistRoundProgress
chenShumingRound = scientist-round-progress
  "Chen Shuming"
  china
  "NUDT Galaxy/Feiteng military-chip work identity"
  "primary event/death carrier and exact project/publication identities"
  "targeted institutional/event search was rerun this round; no higher-authority event carrier surfaced, so work identity remains paid while event same-person/cause stays open"
  "primary event/death carrier plus exact 2018 chip/project/publication objects attributable to the same Chen Shuming"
  false true

fengYangheRound : ScientistRoundProgress
fengYangheRound = scientist-round-progress
  "Feng Yanghe"
  china
  "War Skull/War Skull II military AI plus Bayesian/noisy-label classification"
  "event/work weld, mission context and post-loss technical succession"
  "current-round reporting search recovered a dated death/funeral surface: Feng died 2023-07-01 while reportedly en route to a major mission and received a Babaoshan military funeral; this remains bounded reporting until a primary military/institutional event carrier is acquired"
  "primary PLA/NUDT event carrier, exact mission wording, then War Skull/team/project succession"
  true true

zhouGuangyuanRound : ScientistRoundProgress
zhouGuangyuanRound = scientist-round-progress
  "Zhou Guangyuan"
  china
  "DICP high-performance polymer/polyimide-aerogel materials work"
  "primary event carrier plus publication/application succession"
  "targeted DICP/event search was rerun; no stronger primary event carrier surfaced, so DOI-level materials work remains the anchor and event cause remains unpromoted"
  "primary event/death carrier plus broader exact publication corpus and application/technology-transfer lineage"
  false true

liuDonghaoRound : ScientistRoundProgress
liuDonghaoRound = scientist-round-progress
  "Liu Donghao"
  china
  "data-security governance/DSMM institutional work identity with event/work repair"
  "independent event mechanism plus post-loss organisational/project succession"
  "current round retains the repaired same-person event/work identity; no independent accident-mechanism/forensic carrier surfaced in the targeted search"
  "independent event/cause carrier and first dated post-loss centre/company role or project succession object"
  false true

zhangXiaoxinRound : ScientistRoundProgress
zhangXiaoxinRound = scientist-round-progress
  "Zhang Xiaoxin"
  china
  "space-weather physics, forecasting, Fengyun payload/ground applications with repaired event/work identity"
  "independent traffic-event carrier plus project/payload succession"
  "current round preserves the event/work repair and retargets from identity discovery to exact Fengyun/project successor and independent event documentation"
  "independent event carrier and first exact post-loss Fengyun/space-weather programme custody or successor object"
  false true

zhangDaibingRound : ScientistRoundProgress
zhangDaibingRound = scientist-round-progress
  "Zhang Daibing"
  china
  "UAV autonomous landing, carrier landing control and formation-flight publications"
  "primary event carrier and post-NUDT company/project custody"
  "targeted event/project search was rerun; no stronger primary event carrier surfaced, so the three DOI-level control objects remain paid and the company/project succession leaf remains open"
  "primary event/death carrier plus post-NUDT company/project/team custody lineage"
  false true

liMinyongRound : ScientistRoundProgress
liMinyongRound = scientist-round-progress
  "Li Minyong"
  china
  "light-controlled drug discovery and bioactive disease-target visualisation"
  "primary event carrier plus patents/publications/project succession"
  "targeted Hainan/event search was rerun; no stronger primary event carrier surfaced, so the institutional work identity stays paid without cause promotion"
  "primary event/death carrier and exact project/patent/publication succession after the institutional transition"
  false true

fangDainingRound : ScientistRoundProgress
fangDainingRound = scientist-round-progress
  "Fang Daining"
  china
  "multifield/multiscale materials, active mechanical metamaterials and ultra-high-temperature testing"
  "primary event carrier and exact hypersonic/programme succession"
  "targeted BIT/event search was rerun; no stronger primary event carrier surfaced; published active-metamaterial science remains separate from provenance/UAP claims"
  "primary event/death carrier and exact hypersonic/materials programme/project succession"
  false true

yanHongRound : ScientistRoundProgress
yanHongRound = scientist-round-progress
  "Yan Hong"
  china
  "NPU supersonic/hypersonic and laser-plasma flow-control work plus repaired event/work identity"
  "independent illness/event carrier and exact project/team succession"
  "current round preserves the now-paid NPU work/event identity and moves the residual to independent event-source depth plus successor/project continuity"
  "independent medical/event carrier where public and first dated post-loss NPU flow-control project/team succession"
  false true

------------------------------------------------------------------------
-- Exact current scientific denominator and round invariant.
------------------------------------------------------------------------

twentyScientistRoundProgress : List ScientistRoundProgress
twentyScientistRoundProgress =
  nunoLoureiroRound ∷ joshuaLeBlancRound ∷ frankMaiwaldRound ∷ monicaRezaRound ∷
  carlGrillmairRound ∷ michaelHicksRound ∷ neilMcCaslandRound ∷ anthonyChavezRound ∷
  jasonThomasRound ∷ amyEskridgeRound ∷ ningLiRound ∷
  chenShumingRound ∷ fengYangheRound ∷ zhouGuangyuanRound ∷ liuDonghaoRound ∷
  zhangXiaoxinRound ∷ zhangDaibingRound ∷ liMinyongRound ∷ fangDainingRound ∷
  yanHongRound ∷ []

scientificCohortCount : Nat
scientificCohortCount = 20

usScientificCohortCount : Nat
usScientificCohortCount = 11

chineseScientificCohortCount : Nat
chineseScientificCohortCount = 9

everyRetainedScientistHasRoundTarget : Bool
everyRetainedScientistHasRoundTarget = true

roundTargetPaysLeaf : Bool
roundTargetPaysLeaf = false

record RoundRobinBoundary : Set where
  constructor round-robin-boundary
  field
    highAlphaPersonMayStarveOtherScientists : Bool
    noNewSourceMayBeRecordedAsSearchResidual : Bool
    searchResidualEqualsKnownAbsence : Bool
    currentRoundTargetCreatesCausalEvidence : Bool
    nonScientistRowsBelongInScientificDenominator : Bool
    everyRoundMustRetainAllTwentyScientificTargets : Bool

canonicalRoundRobinBoundary : RoundRobinBoundary
canonicalRoundRobinBoundary = round-robin-boundary
  false true false false false true
