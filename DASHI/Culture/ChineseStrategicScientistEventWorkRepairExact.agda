module DASHI.Culture.ChineseStrategicScientistEventWorkRepairExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Culture.ChineseStrategicScientistRosterSnowballExact as Roster
import DASHI.Physics.Aerospace.YanHongHypersonicFlowControlBidiExact as Yan

------------------------------------------------------------------------
-- EVENT/WORK REPAIR LAYER
--
-- Event identity and technical work identity are paid only where a source chain
-- supplies the same named person plus institution/role continuity.  Reported
-- cause wording is retained separately and does not become forensic causation.
------------------------------------------------------------------------

data RepairStrength : Set where
  exactInstitutional sameInstitutionRepublished boundedSecondary : RepairStrength

record EventWorkRepair : Set where
  constructor event-work-repair
  field
    person : String
    rosterWorkReference : String
    eventReference : String
    eventDate : String
    reportedCauseWording : String
    sourceClass : RepairStrength
    samePersonWorkEventPaid : Bool
    causeMannerForensicPaid : Bool
    commonCausePaid : Bool
    nextLeaf : String

open EventWorkRepair public

yanHongRepair : EventWorkRepair
yanHongRepair = event-work-repair
  "Yan Hong / 严红"
  "Yan.canonical work receipts: DOI 10.7638/kqdlxxb-2013.0102; DOI 10.19527/j.cnki.2096-1642.2018.02.001; NPU laser-plasma flow-control programme"
  "NPU School of Power and Energy obituary republished by ScienceNet"
  "2026-03-24 17:19"
  "因病医治无效 / died after illness despite treatment"
  sameInstitutionRepublished
  true false false
  "project/grant/application succession after 2026-03-24; preserve illness wording as obituary statement, not independent forensic finding"

liuDonghaoRepair : EventWorkRepair
liuDonghaoRepair = event-work-repair
  "Liu Donghao / 刘东昊"
  "Guizhou Big Data Security Engineering Research Center founder/executive and data-security governance identity"
  "Big Data Security Engineering Research Center (Guizhou) company obituary, contemporaneously republished by National Business Daily and Securities Times"
  "2024-03-05"
  "因意外离世 / died following an accident; public obituary did not supply mechanism"
  sameInstitutionRepublished
  true false false
  "exact accident/event carrier if public; DSMM/project custody and organisational succession after death"

zhangXiaoxinRepair : EventWorkRepair
zhangXiaoxinRepair = event-work-repair
  "Zhang Xiaoxin / 张效信"
  "National Satellite Meteorological Center / National Space Weather Monitoring and Warning Center researcher and programme builder"
  "NSMC obituary reproduced by The Paper and other outlets"
  "2024-12-15 18:58"
  "遭遇交通事故 / traffic accident"
  sameInstitutionRepublished
  true false false
  "exact traffic-accident carrier if public; specific project/award identifiers and post-loss monitoring-warning programme succession"

zhouGuangyuanRepair : EventWorkRepair
zhouGuangyuanRepair = event-work-repair
  "Zhou Guangyuan / 周光远"
  "Dalian Institute of Chemical Physics high-performance polymer-materials research identity; DOI 10.1016/j.cej.2023.147642 plus centre/team/application work"
  "Chinese Academy of Sciences / Dalian Institute of Chemical Physics memorial feature republishing China Science Daily material"
  "2023-12-16"
  "逝世 / died; the cited memorial feature does not provide an independent forensic cause"
  exactInstitutional
  true false false
  "recover exact post-loss centre leadership, project/IP custody and continuation of the polyimide-aerogel/high-performance-polymer application programmes"

liMinyongRepair : EventWorkRepair
liMinyongRepair = event-work-repair
  "Li Minyong / 李敏勇"
  "Hainan University medicinal-chemistry identity: light-controlled drug discovery and bioactive disease-target visualisation"
  "Hainan University School of Pharmaceutical Sciences obituary, republished by Beijing Daily"
  "2025-11-16"
  "在广州突发疾病，经抢救无效 / sudden illness in Guangzhou; died despite rescue efforts"
  sameInstitutionRepublished
  true false false
  "recover direct Hainan obituary manifestation plus first post-loss project/patent/student succession object; obituary wording is not an independent medical-forensic finding"

fangDainingRepair : EventWorkRepair
fangDainingRepair = event-work-repair
  "Fang Daining / 方岱宁"
  "BIT advanced-materials and structural-mechanics identity; active mechanical metamaterials and ultra-high-temperature multi-field testing"
  "Chinese Academy of Sciences memorial page for Fang Daining"
  "2026-02-27"
  "因病去世 / died of illness"
  exactInstitutional
  true false false
  "first dated post-loss BIT/Peking advanced-structure project/team leadership and custody object; keep metamaterial science separate from provenance/UAP claims"

zhangDaibingRepair : EventWorkRepair
zhangDaibingRepair = event-work-repair
  "Zhang Daibing / 张代兵"
  "NUDT unmanned-systems research identity plus DOI-level UAV landing/control/formation publications"
  "South China Morning Post 2025-01-08 reporting based on an obituary"
  "2025-01-03"
  "cause not stated in cited obituary/reporting"
  boundedSecondary
  true false false
  "recover the primary obituary/company carrier and named successor/custodian for Yunzhihang and NUDT unmanned-system projects before promoting succession or cause"

------------------------------------------------------------------------
-- Repairs collapse identity debt, not causal or forensic debt.
------------------------------------------------------------------------

record EventWorkRepairBoundary : Set where
  constructor event-work-repair-boundary
  field
    institutionalObituaryCanPaySamePersonContinuity : Bool
    obituaryCauseWordingEqualsIndependentForensicFinding : Bool
    samePersonContinuityPaysCommonCause : Bool
    repairedLeafShouldDropFromIdentityFirstFront : Bool

canonicalEventWorkRepairBoundary : EventWorkRepairBoundary
canonicalEventWorkRepairBoundary = event-work-repair-boundary
  true false false true
