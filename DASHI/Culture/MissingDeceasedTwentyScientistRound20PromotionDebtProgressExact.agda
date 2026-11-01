module DASHI.Culture.MissingDeceasedTwentyScientistRound20PromotionDebtProgressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record Round20PromotionDebtProgress : Set where
  constructor round20-promotion-debt-progress
  field
    person : String
    strongestProgrammeObject : String
    strongestCrossPersonEdge : String
    currentPromotionDebt : String
    nextH2Leaf : String
    nextH3Leaf : String
    h2Paid : Bool
    h3Paid : Bool

open Round20PromotionDebtProgress public

nuno = round20-promotion-debt-progress "Nuno F. G. Loureiro" "MIT PSFC / Viriato-KREHM plasma science carrier" "strategic fusion/aerospace adjacency only" "no second retained person on one literal object" "grant/facility/work-package naming another retained scientist" "operational action tied to that paid shared object" false false
leblanc = round20-promotion-debt-progress "Joshua Kyle LeBlanc" "NASA FSP I&C / WBS 658133.04.01.22.01.06" "NASA programme adjacency only" "same-work-package second retained person unpaid" "exact FSP/TechMat roster or work package naming another retained scientist" "pre-event action/security receipt on shared FSP object" false false
maiwald = round20-promotion-debt-progress "Frank W. Maiwald" "JPL SURP SP23012 / spectroscopy" "JPL institutional edge to Hicks" "shared JPL project/instrument unpaid" "JPL instrument/procurement/work-package naming Hicks or another retained scientist" "pre-event action tied to shared JPL object" false false
reza = round20-promotion-debt-progress "Monica Jacinto / Monica Reza" "Mondaloy patent/process lineage and later AFRL procurement" "intermediated Hardwick-AFRL-McCasland chain" "direct same-programme Reza-McCasland receipt unpaid" "pre-2013 Mondaloy contract/review/tasking naming McCasland" "operational action against both tied to that object" false false
grillmair = round20-promotion-debt-progress "Carl J. Grillmair" "Caltech/IPAC stellar-stream survey carrier" "institution/ecosystem adjacency only" "same survey/work-package second retained person unpaid" "survey/catalogue/project identifier naming another retained scientist" "pre-event operational receipt on that survey object" false false
hicks = round20-promotion-debt-progress "Michael David Hicks" "JPL small-body observing carrier" "JPL institutional edge to Maiwald" "shared JPL object unpaid" "mission/instrument/work-package naming Maiwald or another retained scientist" "pre-event action tied to shared JPL object" false false
mccasland = round20-promotion-debt-progress "William Neil McCasland" "AFRL command/Space Vehicles chronology" "intermediated Mondaloy institutional chain" "specific Mondaloy/Reza tasking or review unpaid" "pre-2013 briefing/contract/programme review naming McCasland" "operational action tied to the same paid object" false false
chavez = round20-promotion-debt-progress "Anthony Chavez" "LANL DARHT/Scorpius carrier" "identity-gated strategic-infrastructure adjacency" "same-person weld precedes common-programme search" "pay missing-person↔LANL identity then search exact task IDs" "cross-case operational evidence only after identity/object payment" false false
thomas = round20-promotion-debt-progress "Jason R. Thomas" "Novartis chemical-biology/signalling carrier" "no cross-person literal edge located" "programme identity unpaid" "grant/consortium/vendor/platform ID naming another retained scientist" "pre-event action on that shared object" false false
amy = round20-promotion-debt-progress "Amy Eskridge" "HAL5/Institute gravity-modification programme carrier" "explicit 2018 reference to Ning Li/Torr AC Gravity" "reference paid; shared programme unpaid" "Amy Institute/NASA release object citing AC Gravity/DAAH01-01-9-R001 or successor apparatus" "operational/security action spanning both on shared object" false false
ning = round20-promotion-debt-progress "Ning Li" "DAAH01-01-9-R001 / AC Gravity" "Amy later references Ning's work" "single-person programme ID strong; second retained person unpaid" "recover SOW/closeout personnel/facility/subcontract table" "pre-event action spanning a second retained participant" false false
chen = round20-promotion-debt-progress "Chen Shuming" "NUDT Galaxy/Feiteng military-DSP carrier" "NUDT institutional edge to Feng/Zhang Daibing" "same military task/work-package unpaid" "primary NUDT/PLA project/task ID naming another retained scientist" "operational/security action on that shared task" false false
feng = round20-promotion-debt-progress "Feng Yanghe" "NUDT War Skull / decision-science carrier" "NUDT institutional edges to Chen/Zhang Daibing" "same task/codebase unpaid" "military task/code/project roster naming Chen or Zhang Daibing" "operational/security action on that shared task" false false
zhou = round20-promotion-debt-progress "Zhou Guangyuan" "DICP DNL2200 polymer-materials centre" "no literal cross-person edge located" "shared project/grant unpaid" "DNL2200 grant/patent/enterprise-transfer identifier naming retained institution/person" "pre-event action on shared object" false false
liu = round20-promotion-debt-progress "Liu Donghao" "Big Data Security Engineering Research Center / DSMM" "no literal cross-person edge located" "national project/task linkage unpaid" "dated national project/company/task identifier naming retained counterpart" "pre-event action on shared object" false false
zhangXiaoxin = round20-promotion-debt-progress "Zhang Xiaoxin" "NSMC/Fengyun space-weather carrier" "aerospace capability adjacency only" "shared payload/project second retained person unpaid" "Fengyun payload/project participant identifier naming another retained scientist" "pre-event action on shared Fengyun object" false false
zhangDaibing = round20-promotion-debt-progress "Zhang Daibing" "NUDT UAV/autonomy carrier" "NUDT institutional edge to Feng/Chen" "same autonomous-system task unpaid" "NUDT task/code/programme roster naming Feng or Chen" "operational/security action on shared task" false false
liMinyong = round20-promotion-debt-progress "Li Minyong" "photopharmacology/probe patent carrier" "no literal cross-person edge located" "shared grant/project unpaid" "grant/patent/project identifier naming retained counterpart" "pre-event action on shared object" false false
fang = round20-promotion-debt-progress "Fang Daining" "BIT advanced-structure/metamaterial carrier" "strategic materials adjacency only" "shared national project/work-package unpaid" "national project/grant participant list naming retained counterpart" "pre-event action on shared object" false false
yan = round20-promotion-debt-progress "Yan Hong" "NPU hypersonic/flow-control carrier" "aerospace capability adjacency only" "shared national hypersonic project unpaid" "NPU/national project participant identifier naming retained counterpart" "pre-event action on shared object" false false

round20All : List Round20PromotionDebtProgress
round20All = nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷ thomas ∷ amy ∷ ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷ zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

round20ScientificCohortCount : Nat
round20ScientificCohortCount = 20

round20EveryScientistTouched : Bool
round20EveryScientistTouched = true

round20H2PromotionCount : Nat
round20H2PromotionCount = 0

round20H3PromotionCount : Nat
round20H3PromotionCount = 0

round20SearchResidualCreatesKnownAbsence : Bool
round20SearchResidualCreatesKnownAbsence = false

round20CapabilityCoveragePaysHistoricalParticipation : Bool
round20CapabilityCoveragePaysHistoricalParticipation = false

round20ProgrammeIdentifierWithoutSecondPersonPaysH2 : Bool
round20ProgrammeIdentifierWithoutSecondPersonPaysH2 = false
