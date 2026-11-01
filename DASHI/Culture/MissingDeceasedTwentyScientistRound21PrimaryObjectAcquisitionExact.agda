module DASHI.Culture.MissingDeceasedTwentyScientistRound21PrimaryObjectAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record Round21PrimaryObjectProgress : Set where
  constructor round21-primary-object-progress
  field
    person : String
    strongestPrimaryObjectState : String
    freshRound21Delta : String
    nextH2Leaf : String
    nextH3Leaf : String
    h2Paid : Bool
    h3Paid : Bool

open Round21PrimaryObjectProgress public

nuno = round21-primary-object-progress "Nuno F. G. Loureiro" "MIT PSFC / Viriato-KREHM science carrier; shared programme object unresolved" "no new literal cross-person identifier promoted" "grant/facility/repository object naming another retained scientist" "pre-event operational action on that paid object" false false
leblanc = round21-primary-object-progress "Joshua Kyle LeBlanc" "NASA FSP I&C WBS 658133.04.01.22.01.06" "single-person work-package remains strong but cohort-shared object unresolved" "exact TechMat/FSP roster or subordinate work package naming another retained scientist" "pre-event security/action receipt on shared FSP object" false false
maiwald = round21-primary-object-progress "Frank W. Maiwald" "JPL SURP SP23012 / action-spectroscopy" "shared JPL employer remains below same-object threshold" "mission/instrument/facility/procurement/work-package naming Hicks or another retained scientist" "pre-event action tied to shared JPL object" false false
reza = round21-primary-object-progress "Monica Jacinto / Monica Reza" "Mondaloy lineage; official SAM.gov FA930020P5032 M200 billet procurement establishes 2020 AFRL programme persistence" "2020 procurement is primary object evidence but cannot retroactively pay McCasland participation" "recover pre-2013 Mondaloy contract/cost-share/review/tasking naming Reza/Hardwick/McCasland roles" "operational action tied to a paid pre-event common object" false false
grillmair = round21-primary-object-progress "Carl J. Grillmair" "Caltech/IPAC stellar-stream survey carrier" "no new literal cohort-shared survey object" "survey/catalogue/programme identifier naming another retained scientist" "pre-event action on that survey object" false false
hicks = round21-primary-object-progress "Michael David Hicks" "JPL small-body observing / 3122 Florence carrier" "JPL cluster remains institutional, not shared project" "exact observing programme/instrument/work-package naming Maiwald or another retained scientist" "pre-event action on shared JPL object" false false
mccasland = round21-primary-object-progress "William Neil McCasland" "official AFRL commander 2011-2013 chronology" "official command interval paid; Mondaloy-specific tasking/review still unpaid" "pre-2013 Mondaloy briefing/contract/programme-review naming McCasland" "operational action tied to the same paid object" false false
chavez = round21-primary-object-progress "Anthony Chavez" "LANL DARHT/Scorpius carrier; identity weld remains prerequisite" "no programme promotion before same-person identity" "pay missing-person↔LANL identity, then enumerate DARHT/Scorpius task identifiers" "cross-case operational evidence only after identity and object payment" false false
thomas = round21-primary-object-progress "Jason R. Thomas" "Novartis macrophage-signalling/ferritinophagy science objects" "no literal cohort-shared programme object located" "grant/consortium/vendor/platform identifier naming another retained scientist" "pre-event action on that paid shared object" false false
amy = round21-primary-object-progress "Amy Eskridge" "HAL5 2018 primary historical reference to Ning Li/Torr AC Gravity" "literal awareness/reference remains paid; programme membership does not" "inspect Institute/NASA-reviewed release object and metadata for AC Gravity, DAAH01-01-9-R001, apparatus/personnel IDs" "operational/security action spanning both on a paid common object" false false
ning = round21-primary-object-progress "Ning Li" "DAAH01-01-9-R001 Army prototype agreement; official FY2001 report locator known, original bytes/SOW/closeout still not inspected" "programme object identity strengthened without second retained person" "materialise original row and recover SOW/closeout personnel, facilities, subcontractors and apparatus" "pre-event action spanning a second retained participant on that object" false false
chen = round21-primary-object-progress "Chen Shuming" "NUDT Galaxy/Feiteng military-DSP lineage" "institutional overlap with Feng/Zhang remains below shared-task threshold" "primary NUDT/PLA task/project/codebase identifier naming another retained scientist" "operational/security action on that paid shared task" false false
feng = round21-primary-object-progress "Feng Yanghe" "NUDT War Skull / decision-science carrier" "institutional overlap remains H1-level" "military task/code/project roster naming Chen or Zhang Daibing" "operational/security action on shared task" false false
zhou = round21-primary-object-progress "Zhou Guangyuan" "DICP DNL2200 high-performance polymer materials centre" "no new cross-cohort object promotion" "grant/patent/enterprise-transfer identifier naming retained counterpart" "pre-event action on shared object" false false
liu = round21-primary-object-progress "Liu Donghao" "Big Data Security Engineering Research Center / DSMM" "governance/project identity remains single-lane" "dated national project/company/task identifier naming retained counterpart" "pre-event action on shared object" false false
zhangXiaoxin = round21-primary-object-progress "Zhang Xiaoxin" "NSMC/Fengyun space-weather programme carrier" "programme family paid, cohort-shared payload/work package unpaid" "exact Fengyun payload/project participant identifier naming another retained scientist" "pre-event action on shared Fengyun object" false false
zhangDaibing = round21-primary-object-progress "Zhang Daibing" "NUDT UAV/autonomy carrier" "NUDT overlap with Chen/Feng remains institutional/project-family only" "exact NUDT task/code/programme roster naming Feng or Chen" "operational/security action on shared task" false false
liMinyong = round21-primary-object-progress "Li Minyong" "photopharmacology/probe patent family" "no literal cohort-shared grant/project object" "grant/patent/project identifier naming retained counterpart" "pre-event action on shared object" false false
fang = round21-primary-object-progress "Fang Daining" "BIT advanced-structure/metamaterial carrier" "no literal cohort-shared national project promoted" "national project/grant participant list naming retained counterpart" "pre-event action on shared object" false false
yan = round21-primary-object-progress "Yan Hong" "NPU hypersonic/flow-control carrier" "no literal cohort-shared national project promoted" "NPU/national project participant identifier naming retained counterpart" "pre-event action on shared object" false false

round21All : List Round21PrimaryObjectProgress
round21All = nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷ thomas ∷ amy ∷ ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷ zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

round21ScientificCohortCount : Nat
round21ScientificCohortCount = 20

round21EveryScientistTouched : Bool
round21EveryScientistTouched = true

round21H2PromotionCount : Nat
round21H2PromotionCount = 0

round21H3PromotionCount : Nat
round21H3PromotionCount = 0

round21PrimaryObjectAcquisitionDoesNotCreateCommonCause : Bool
round21PrimaryObjectAcquisitionDoesNotCreateCommonCause = false

round21SearchResidualCreatesKnownAbsence : Bool
round21SearchResidualCreatesKnownAbsence = false

round21LaterProgrammePersistenceDoesNotPayEarlierParticipation : Bool
round21LaterProgrammePersistenceDoesNotPayEarlierParticipation = false

round21PrimaryLocatorDoesNotEqualPrimaryByteCustody : Bool
round21PrimaryLocatorDoesNotEqualPrimaryByteCustody = false
