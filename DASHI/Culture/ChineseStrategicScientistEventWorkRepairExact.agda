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
