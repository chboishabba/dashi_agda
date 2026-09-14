module DASHI.Culture.MissingDeceasedTwentyScientistRound16LiteralObjectProgressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record Round16LiteralObjectProgress : Set where
  constructor round16-literal-object-progress
  field
    person : String
    strongestLiteralObject : String
    evidenceRung : String
    sameProgrammePaid : Bool
    nextObjectAcquisition : String
    nextEventDiscriminator : String

open Round16LiteralObjectProgress public

nuno = round16-literal-object-progress "Nuno F. G. Loureiro" "MIT PSFC / Viriato-KREHM scientific carrier" "science object; no cohort-shared programme ID" false "recover exact grants/repository stewardship/facility identifiers and search for another retained scientist on the same object" "event timing remains downstream of literal shared-object evidence"
leblanc = round16-literal-object-progress "Joshua Kyle LeBlanc" "Fission Surface Power I&C WBS 658133.04.01.22.01.06" "literal single-person work-package identifier" false "recover post-loss TechMat roster, partner organisations and subordinate work-package IDs" "test chronology against an actual handoff, not generic NASA overlap"
maiwald = round16-literal-object-progress "Frank W. Maiwald" "JPL SURP SP23012 / tagged-ion action spectroscopy" "literal project identifier; JPL overlap with Hicks only institutional" false "recover procurement/instrument/work-package identifiers and collaborator rosters" "institutional clustering does not pay project-linked event alignment"
reza = round16-literal-object-progress "Monica Jacinto / Monica Reza" "Mondaloy lineage + later AFRL procurement FA930020P5032" "literal material/procurement object; direct Reza-McCasland same programme unpaid" false "recover pre-2013 AFRL Mondaloy contract/work-package/programme-review IDs and named participants" "later 2020 procurement cannot retroactively create 2011-2013 McCasland involvement"
grillmair = round16-literal-object-progress "Carl J. Grillmair" "IPAC/Caltech stellar-stream survey/catalogue carrier" "science/survey object only" false "recover exact survey/catalogue/program identifiers shared with another retained scientist" "retain ordinary-event explanations unless a pre-event object edge appears"
hicks = round16-literal-object-progress "Michael David Hicks" "JPL small-body observing / 3122 Florence campaign carrier" "campaign object; JPL overlap with Maiwald only institutional" false "recover exact observing-program/work-package/procurement identifiers and participant list" "do not promote same employer into causal linkage"
mccasland = round16-literal-object-progress "William Neil McCasland" "AFRL command / Space Vehicles chronology" "institutional authority; no acquired Mondaloy work-package naming him" false "search 1999-2013 AFRL Mondaloy programme reviews/contracts/briefings for named leadership or approval chain" "command hierarchy and same-date coincidence remain non-causal"
chavez = round16-literal-object-progress "Anthony Chavez" "LANL DARHT/Scorpius engineering carrier" "identity-gated science object" false "first pay missing-person/LANL same-person identity; then enumerate DARHT/Scorpius task IDs and partners" "event chronology cannot inherit LANL programme evidence before identity weld"
thomas = round16-literal-object-progress "Jason R. Thomas" "Novartis macrophage signalling / ferritinophagy assay objects" "science objects only" false "recover grant/project/assay-platform/vendor identifiers and collaboration rosters" "cause/manner and lab succession remain separate from technical adjacency"
amy = round16-literal-object-progress "Amy Eskridge" "HAL5 2018 explicit Ning Li/Torr historical reference; Institute gravity-modification programme" "literal person-reference, not same programme" false "inspect Amy NASA/Institute reviewed object and release metadata for AC Gravity, DAAH01-01-9-R001, apparatus or personnel IDs" "awareness/reference does not establish shared targeting or programme membership"
ning = round16-literal-object-progress "Ning Li" "DAAH01-01-9-R001 / Gravito-Electro Magnetic Superconductivity Experiment" "literal Army programme/object identifier" false "acquire original FY2001 row bytes, SOW and closeout; enumerate named people, facilities, subcontractors and apparatus" "programme existence does not establish success, disappearance or coordinated targeting"
chen = round16-literal-object-progress "Chen Shuming" "NUDT Galaxy/Feiteng military-DSP lineage" "institutional/project lineage; no cohort-shared task ID" false "recover exact national/NUDT task numbers, chip programme IDs and participant rosters" "event identity/cause must be sourced independently"
feng = round16-literal-object-progress "Feng Yanghe" "NUDT War Skull / military-intelligence decision-science carrier" "institutional/project lineage; no cohort-shared task ID" false "recover War Skull military task/code/work-package IDs and named cross-institute participants" "strategic mission does not imply common event cause"
zhou = round16-literal-object-progress "Zhou Guangyuan" "DICP DNL2200 high-performance polymer materials centre" "literal centre identifier; no cohort-shared programme" false "recover DNL2200 grant/patent/enterprise-transfer IDs and partner institutions" "post-loss centre succession does not establish cause"
liu = round16-literal-object-progress "Liu Donghao" "Big Data Security Engineering Research Center / DSMM" "centre/governance identifier only" false "date company/governance transition and recover national project/task identifiers" "role transition does not imply targeted disruption"
zhangXiaoxin = round16-literal-object-progress "Zhang Xiaoxin" "NSMC/Fengyun space-weather carrier" "programme family identifier; no cohort-shared work package" false "recover exact Fengyun payload/project IDs and cross-institution participant lists" "stale committee pages/posthumous publication do not create programme-event linkage"
zhangDaibing = round16-literal-object-progress "Zhang Daibing" "NUDT UAV/autonomous-landing/robotics carrier" "institutional/project lineage; no shared task with Chen/Feng yet" false "recover exact NUDT unmanned-systems programme/task/code IDs and participant roster" "institutional clustering remains H1-level evidence"
liMinyong = round16-literal-object-progress "Li Minyong" "photopharmacology / fluorescent-probe patent family" "patent/science object only" false "recover grant/project/patent co-custody IDs and collaborating institutions" "lab/project succession does not imply event cause"
fang = round16-literal-object-progress "Fang Daining" "BIT advanced-structure/metamaterial inverse-design programme carrier" "science/institute object; no cohort-shared programme ID" false "recover national grant/project IDs, unit-cell project records and partner institutions" "distributed pre-loss leadership weakens single-point-loss inference"
yan = round16-literal-object-progress "Yan Hong" "NPU hypersonic thermal/plasma flow-control carrier" "science/programme family only" false "recover exact NPU/national project IDs, facility IDs and partner institutions" "stale profile/committee surfaces do not pay post-loss linkage"

round16All : List Round16LiteralObjectProgress
round16All = nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷ thomas ∷ amy ∷ ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷ zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

round16ScientificCohortCount : Nat
round16ScientificCohortCount = 20

round16EveryScientistTouched : Bool
round16EveryScientistTouched = true

round16H2PromotionCount : Nat
round16H2PromotionCount = 0

round16H3PromotionCount : Nat
round16H3PromotionCount = 0

round16LiteralObjectIdentifiersCanGuideSearch : Bool
round16LiteralObjectIdentifiersCanGuideSearch = true

round16InstitutionalAdjacencyPaysSameProgramme : Bool
round16InstitutionalAdjacencyPaysSameProgramme = false

round16SearchResidualCreatesKnownAbsence : Bool
round16SearchResidualCreatesKnownAbsence = false
