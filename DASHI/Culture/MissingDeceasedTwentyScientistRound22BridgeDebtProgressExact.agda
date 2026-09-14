module DASHI.Culture.MissingDeceasedTwentyScientistRound22BridgeDebtProgressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record Round22BridgeProgress : Set where
  constructor round22-bridge-progress
  field
    person : String
    closestCurrentBridge : String
    currentPaymentState : String
    nextLiteralPayment : String
    nextEventLinkLeaf : String
    h2Paid : Bool
    h3Paid : Bool

open Round22BridgeProgress public

nuno = round22-bridge-progress "Nuno F. G. Loureiro" "MIT PSFC / Viriato-KREHM science carrier" "science and institution paid; no retained-person same-object bridge" "exact shared grant/repository/facility/work package with retained cohort" "event chronology only after literal object bridge" false false
leblanc = round22-bridge-progress "Joshua Kyle LeBlanc" "FSP I&C WBS 658133.04.01.22.01.06" "strong programme object, second retained person unpaid" "named partner/work package intersecting retained cohort" "test event/handoff ordering only after cross-person weld" false false
maiwald = round22-bridge-progress "Frank W. Maiwald" "JPL/SURP spectroscopy carrier" "JPL cluster with Hicks paid; shared object unpaid" "mission/instrument/facility/procurement/work-package naming both" "keep institutional clustering distinct from event linkage" false false
reza = round22-bridge-progress "Monica Jacinto / Monica Reza" "Mondaloy lineage; FA930020P5032 later procurement" "AFRL programme persistence paid; McCasland-specific programme role unpaid" "pre-2013 contract/review/tasking naming Reza/Hardwick object and McCasland role" "event link forbidden until same-object role is paid" false false
grillmair = round22-bridge-progress "Carl J. Grillmair" "IPAC stellar-stream/survey carrier" "science/institution paid; no cohort same-object bridge" "shared survey/catalogue/work package with retained cohort" "retain ordinary-event explanations as control" false false
hicks = round22-bridge-progress "Michael David Hicks" "JPL small-body observing carrier" "JPL cluster with Maiwald paid; shared object unpaid" "same JPL mission/instrument/facility/work package as Maiwald" "do not convert employer overlap into event cause" false false
mccasland = round22-bridge-progress "William Neil McCasland" "AFRL commander 2011-2013" "command authority paid; Mondaloy-specific participation unpaid" "briefing/approval/review/tasking naming McCasland and Mondaloy/Reza object" "same date/command hierarchy are not targeting evidence" false false
chavez = round22-bridge-progress "Anthony Chavez" "LANL DARHT/Scorpius science carrier" "technical carrier exists; missing-person same-person weld still gated" "first pay identity, then exact task/facility bridge" "event cannot inherit LANL science before identity payment" false false
thomas = round22-bridge-progress "Jason R. Thomas" "chemical-biology signalling/ferritinophagy carrier" "science paid; no cohort same-object bridge" "grant/consortium/vendor/assay-platform identifier shared with retained cohort" "cause/manner and project succession remain separate" false false
amy = round22-bridge-progress "Amy Eskridge" "HAL5 2018 explicit Ning Li/Torr reference" "literal historical person/work reference paid; programme membership unpaid" "Amy Institute/NASA-reviewed object or correspondence carrying AC Gravity/Army identifier" "awareness/reference does not pay targeting" false false
ning = round22-bridge-progress "Ning Li" "DAAH01-01-9-R001" "single-person programme identifier paid; primary SOW/closeout custody and second retained person unpaid" "inspect original row/SOW/closeout and enumerate people/facilities/subcontracts/apparatus" "only then test pre-event cross-case operational linkage" false false
chen = round22-bridge-progress "Chen Shuming" "NUDT Galaxy/Feiteng carrier" "shared NUDT institution with Feng/Zhang; same task unpaid" "exact PLA/NUDT task/project/lab/code identifier naming another retained scientist" "institutional mission is not event cause" false false
feng = round22-bridge-progress "Feng Yanghe" "NUDT War Skull / decision-science carrier" "shared NUDT institution; same task/code unpaid" "exact task/code/work package naming Chen or Zhang Daibing" "event relation waits on same-object edge" false false
zhou = round22-bridge-progress "Zhou Guangyuan" "DICP DNL2200 centre" "centre/project science paid; no cohort same-object bridge" "grant/patent/enterprise-transfer partner identifier intersecting retained cohort" "succession does not imply cause" false false
liu = round22-bridge-progress "Liu Donghao" "Big Data Security Engineering Research Center / DSMM" "institution/company surfaces paid; cross-cohort object unpaid" "dated national project/company/task identifier shared with retained cohort" "governance transition remains separate from event cause" false false
zhangXiaoxin = round22-bridge-progress "Zhang Xiaoxin" "NSMC/Fengyun space-weather carrier" "programme science paid; retained-person same-object bridge unpaid" "payload/project/work package and participant roster intersecting cohort" "posthumous publication/stale page cannot pay cause" false false
zhangDaibing = round22-bridge-progress "Zhang Daibing" "NUDT UAV/autonomy carrier" "shared NUDT institution with Chen/Feng; same task unpaid" "exact task/code/project identifier naming Chen/Feng or another retained scientist" "event link waits on project identity" false false
liMinyong = round22-bridge-progress "Li Minyong" "photopharmacology/probe patent carrier" "science/project identifiers exist; cross-cohort object unpaid" "grant/patent co-custody or platform identifier shared with cohort" "lab succession is not targeting" false false
fang = round22-bridge-progress "Fang Daining" "BIT advanced-structure/metamaterial carrier" "science and distributed leadership paid; cross-cohort object unpaid" "national project/grant/work package naming retained partner" "distributed leadership weakens single-point-loss inference" false false
yan = round22-bridge-progress "Yan Hong" "NPU hypersonic/flow-control carrier" "science/institution paid; cross-cohort object unpaid" "national project/task and partner roster intersecting cohort" "stale surfaces cannot pay post-loss linkage" false false

round22All : List Round22BridgeProgress
round22All = nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷ thomas ∷ amy ∷ ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷ zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

round22ScientificCohortCount : Nat
round22ScientificCohortCount = 20

round22EveryScientistTouched : Bool
round22EveryScientistTouched = true

round22H2PromotionCount : Nat
round22H2PromotionCount = 0

round22H3PromotionCount : Nat
round22H3PromotionCount = 0

round22SearchResidualCreatesKnownAbsence : Bool
round22SearchResidualCreatesKnownAbsence = false

round22ClosestCurrentH2Leaves : String
round22ClosestCurrentH2Leaves =
  "JPL exact shared work package; NUDT exact shared task/code; DAAH01-01-9-R001 primary SOW/closeout personnel; Amy reviewed-object cross-reference; pre-2013 Mondaloy programme record"
