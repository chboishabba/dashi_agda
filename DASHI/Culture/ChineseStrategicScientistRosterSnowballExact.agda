module DASHI.Culture.ChineseStrategicScientistRosterSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CHINESE STRATEGIC-SCIENTIST ROSTER SNOWBALL
--
-- The media roster is discovery-only.  Each technical-work identity is followed
-- outward into institutional/publication objects independently of the event
-- identity.  A media list cannot weld work, event, cause, or cross-national
-- common-cause claims.
------------------------------------------------------------------------

data WorkSourceStrength : Set where
  mediaOnly primaryInstitutional primaryPublication primaryPublisher : WorkSourceStrength

record ChineseStrategicScientistWork : Set where
  constructor chinese-strategic-scientist-work
  field
    person : String
    mediaRosterField : String
    workIdentity : String
    workObject : String
    workMethodOrCapability : String
    workSource : String
    workSourceStrength : WorkSourceStrength
    workIdentityPaid : Bool
    eventIdentitySamePersonPaid : Bool
    eventCausePrimaryPaid : Bool
    stableIdentifier : String
    qidCoordinate : String
    deweyTraversal : String
    nextExactLeaf : String

open ChineseStrategicScientistWork public

chenShuming : ChineseStrategicScientistWork
chenShuming = chinese-strategic-scientist-work
  "Chen Shuming"
  "microelectronics / military chips"
  "Chen Shuming, NUDT Galaxy-Feiteng chip-team technical backbone"
  "domestic military DSP / flight-control processor development"
  "logic analysis, functional verification and autonomous military-chip development under supply blockade"
  "National University of Defense Technology 2026-01-29 Galaxy-Feiteng team history"
  primaryInstitutional
  true false false
  "institutional article; exact historical chip/project identifier unresolved"
  "unresolvedQid"
  "621.3815 Microelectronics / 623 Military engineering traversal only"
  "primary event/death carrier and exact 2018 project/publication objects attributable to this Chen Shuming"

fengYanghe : ChineseStrategicScientistWork
fengYanghe = chinese-strategic-scientist-work
  "Feng Yanghe"
  "military AI / simulation"
  "Feng Yanghe, NUDT System Engineering"
  "War Skull / War Skull II intelligent wargame agents; Bayesian and noisy-label classification"
  "opponent-adaptive task-level decision modules; multi-group graph Bayesian classification; robust classification under label noise"
  "NUDT 2020-12-29 War Skull II; NUDT Press ISBN 978-7-5673-0533-5 (2019); ISBN 978-7-5673-0611-0 (2023)"
  primaryInstitutional
  true false false
  "ISBN 978-7-5673-0533-5; ISBN 978-7-5673-0611-0"
  "unresolvedQid"
  "355.4 Military operations / 006.3 AI / 519.5 Statistics traversal only"
  "primary event/death carrier and exact same-person weld from event identity to NUDT work identity"

zhouGuangyuan : ChineseStrategicScientistWork
zhouGuangyuan = chinese-strategic-scientist-work
  "Zhou Guangyuan"
  "chemistry / polymers / materials"
  "Zhou Guangyuan, Dalian Institute of Chemical Physics high-performance polymer materials"
  "polyimide aerogels for high-temperature thermal insulation"
  "benzhydrylidenefluorene-based diamine design; low shrinkage, high porosity and thermal insulation"
  "DICP institutional research page for polyimide aerogels; Chemical Engineering Journal"
  primaryInstitutional
  true false false
  "DOI 10.1016/j.cej.2023.147642"
  "unresolvedQid"
  "668.4 Polymers / 620.11 Engineering materials traversal only"
  "primary event/death carrier plus broader exact publication corpus and application/technology-transfer lineage"

liuDonghao : ChineseStrategicScientistWork
liuDonghao = chinese-strategic-scientist-work
  "Liu Donghao"
  "data/security systems"
  "Liu Donghao, Guizhou Big Data Security Engineering Research Center candidate identity"
  "data-security governance and DSMM capability maturity implementation"
  "national-standard-driven security governance across collection, transmission, storage, processing, exchange and destruction"
  "Shenzhen Institute of Data Economy / CUHK-Shenzhen 2022-07-11 lecture and transcript"
  primaryInstitutional
  true false false
  "GB/T 37988-2019 DSMM named work context; person stable identifier unresolved"
  "unresolvedQid"
  "005.8 Data security / 658.4 Management traversal only"
  "same-person weld between media event identity and this institutional Liu Donghao before inheriting the work"

zhangXiaoxin : ChineseStrategicScientistWork
zhangXiaoxin = chinese-strategic-scientist-work
  "Zhang Xiaoxin"
  "space weather / monitoring / warning"
  "Zhang Xiaoxin, National Satellite Meteorological Center / space-weather programme"
  "space-weather physics, forecasting models, Fengyun satellite payloads and ground application systems"
  "solar-wind/near-Earth interaction; quantitative forecasting; satellite space-weather monitoring and warning"
  "NSMC space-weather committee and 2022 twenty-year space-weather programme history"
  primaryInstitutional
  true false false
  "SAT/TC347/SC3 committee role; exact person identifier unresolved"
  "unresolvedQid"
  "551.5 Meteorology / 523.9 Space physics traversal only"
  "primary event/death carrier and exact award/project identifiers behind military science-and-technology progress reporting"

zhangDaibing : ChineseStrategicScientistWork
zhangDaibing = chinese-strategic-scientist-work
  "Zhang Daibing"
  "unmanned systems / drones"
  "Zhang Daibing, NUDT unmanned-system researcher"
  "UAV autonomous landing, carrier landing control, formation flight and autonomous control"
  "multisensor fusion, high-disturbance flight control, formation test systems, path following"
  "Journal of NUDT / BUAA / Robot publications plus institutional lecture biography"
  primaryPublication
  true false false
  "DOI 10.11887/j.cn.201801023; DOI 10.13700/j.bh.1001-5965.2016.0679; DOI 10.13973/j.cnki.robot.2017.0160"
  "unresolvedQid"
  "629.132 Unmanned aircraft / 629.8 Automatic control traversal only"
  "primary event/death carrier and post-NUDT company/project custody lineage"

liMinyong : ChineseStrategicScientistWork
liMinyong = chinese-strategic-scientist-work
  "Li Minyong"
  "medicinal chemistry / biomedical visualisation"
  "Li Minyong, Hainan University School of Pharmaceutical Sciences"
  "light-controlled drug discovery and bioactive visualisation of disease target proteins"
  "photocontrol, molecular visualisation, medicinal chemistry and target-protein imaging"
  "Hainan University faculty profile 2025-04-16"
  primaryInstitutional
  true false false
  "institutional profile; publication DOI corpus not yet source-attributed here"
  "unresolvedQid"
  "615.19 Pharmaceutical chemistry / 572 Biochemistry traversal only"
  "primary event/death carrier and exact project/patent/publication succession after 2025 institutional transition"

fangDaining : ChineseStrategicScientistWork
fangDaining = chinese-strategic-scientist-work
  "Fang Daining"
  "hypersonics / advanced materials / structural mechanics"
  "Fang Daining, Beijing Institute of Technology Institute of Advanced Structure Technology"
  "multifield multiscale advanced materials, active mechanical metamaterials and ultra-high-temperature testing"
  "electro-magneto-thermo-mechanical multiscale mechanics; phase-transition/strain-mismatch/instability metamaterials; 1800-2300 C extreme-environment testing"
  "BIT institutional faculty/research pages 2016-2021"
  primaryInstitutional
  true false false
  "institutional work corpus; exact publication DOI set unresolved in this owner"
  "unresolvedQid"
  "620.11 Engineering materials / 531 Mechanics / 629.1 Aerospace traversal only"
  "primary event/death carrier and exact hypersonic-program/project lineage; keep published metamaterial science separate from provenance claims"

yanHong : ChineseStrategicScientistWork
yanHong = chinese-strategic-scientist-work
  "Yan Hong"
  "hypersonics / propulsion"
  "Yan Hong, Northwestern Polytechnical University candidate work identity"
  "supersonic/hypersonic flow control, plasma flow control and computational fluid dynamics"
  "flow-control methods relevant to next-generation aerospace propulsion"
  "NPU obituary/work summary as reported by SCMP; exact primary NPU work page still to acquire"
  mediaOnly
  false false false
  "exact DOI/project identifiers unresolved"
  "unresolvedQid"
  "629.134 Aerospace propulsion / 532 Fluid mechanics traversal only"
  "primary NPU faculty/project/publication carrier, then exact event/death same-person weld"

------------------------------------------------------------------------
-- The nine named cases do not license an invented tenth identity.
------------------------------------------------------------------------

ninthNamedCaseDoesNotCreateTenth : Bool
ninthNamedCaseDoesNotCreateTenth = true

record ChineseRosterBoundary : Set where
  constructor chinese-roster-boundary
  field
    mediaRosterCreatesPersonIdentity : Bool
    sharedStrategicFieldCreatesCommonCause : Bool
    primaryWorkMayBeAcquiredBeforeEventWeld : Bool
    workMayBeRetainedWithoutPromotingEventCause : Bool
    usAndChinaRostersMayBeMergedByNarrative : Bool
    exactCrossNationalMechanismStillRequired : Bool

canonicalChineseRosterBoundary : ChineseRosterBoundary
canonicalChineseRosterBoundary = chinese-roster-boundary
  false false true true false true
