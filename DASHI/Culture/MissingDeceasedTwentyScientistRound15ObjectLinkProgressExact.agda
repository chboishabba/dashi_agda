module DASHI.Culture.MissingDeceasedTwentyScientistRound15ObjectLinkProgressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record Round15ObjectLinkProgress : Set where
  constructor round15-object-link-progress
  field
    person : String
    strongestCurrentObjectIdentifier : String
    strongestCrossPersonRelation : String
    commonProgrammeReceiptPaid : Bool
    nextLiteralObjectLeaf : String
    nextEventLinkLeaf : String

open Round15ObjectLinkProgress public

nuno = round15-object-link-progress "Nuno F. G. Loureiro" "MIT PSFC / Viriato-KREHM scientific carrier" "strategic fusion/aerospace-sector adjacency only" false "find a literal grant/work-package/facility identifier shared with another retained scientist" "compare event chronology only after a same-object edge exists"
leblanc = round15-object-link-progress "Joshua Kyle LeBlanc" "NASA Fission Surface Power I&C, WBS 658133.04.01.22.01.06" "NASA/aerospace portfolio adjacency; no retained-person same-work-package receipt" false "post-loss TechMat roster plus exact project/work-package partners" "test whether any event precedes or follows an actual I&C handoff"
maiwald = round15-object-link-progress "Frank W. Maiwald" "JPL SURP SP23012 / action-spectroscopy lineage" "same JPL institution as Hicks; distinct public science objects" false "JPL work-package/procurement or instrument identifier naming another retained scientist" "separate institutional clustering from project-level event alignment"
reza = round15-object-link-progress "Monica Jacinto / Monica Reza" "Mondaloy patent/process lineage; AFRL later procurement FA930020P5032" "intermediated Reza-Hardwick-AFRL-McCasland command chain; direct Reza-McCasland work unpaid" false "recover pre-2013 Mondaloy AFRL contract/work-package numbers and named programme participants" "align disappearance only after a literal programme/custody edge is paid"
grillmair = round15-object-link-progress "Carl J. Grillmair" "Caltech/IPAC stellar-stream and survey science carrier" "Caltech/JPL ecosystem adjacency only" false "find same survey/catalogue/work-package identifier with another retained scientist" "retain charged local-crime chronology as strong ordinary-event control"
hicks = round15-object-link-progress "Michael David Hicks" "JPL small-body/DART/DS1 observing carrier" "same JPL institution as Maiwald; no shared public project located" false "recover exact project/work-package/procurement overlap with another retained scientist" "keep known health/natural-cause or ordinary explanations separate from programme hypotheses"
mccasland = round15-object-link-progress "William Neil McCasland" "AFRL command / Space Vehicles chronology" "institutional command path to Mondaloy via AFRL and Dallis Hardwick; direct Reza work unpaid" false "recover an actual briefing, contract, programme review or tasking document naming McCasland and Mondaloy/Reza" "do not use same-date or command hierarchy as targeting evidence"
chavez = round15-object-link-progress "Anthony Chavez" "LANL DARHT/Scorpius engineering carrier, identity weld still gated" "New Mexico strategic-infrastructure adjacency only until identity paid" false "first pay same-person weld, then search Scorpius/DARHT task identifiers shared with retained cohort" "missing-person chronology cannot inherit LANL science before identity weld"
thomas = round15-object-link-progress "Jason R. Thomas" "Novartis chemical-biology / signalling assay carrier" "no literal programme relation to current cohort located" false "search grants, consortia, vendors or assay-platform identifiers before thematic biology links" "event cause/manner and lab succession remain separate"
amy = round15-object-link-progress "Amy Eskridge" "HAL5/Institute gravity-modification programme carrier" "explicitly references Ning Li/Torr/AC Gravity in 2018 HAL5 deck" false "search whether Amy's Institute/NASA-reviewed object cites or contracts with AC Gravity/DAAH01-01-9-R001 successors" "public awareness of Ning does not pay shared programme or targeting"
ning = round15-object-link-progress "Ning Li" "Army OTA DAAH01-01-9-R001 / AC Gravity" "Amy later references Ning's work; no shared contract/team receipt" false "recover primary FY2001 row, SOW, closeout and all named personnel/subcontract/facility identifiers" "death and later public rediscovery are not disappearance/targeting evidence"
chen = round15-object-link-progress "Chen Shuming" "NUDT Galaxy/Feiteng military-DSP carrier" "same NUDT institution as Feng and Zhang Daibing; distinct public objects" false "search exact NUDT task/project identifier shared with another retained scientist" "event/death identity must be sourced independently of institutional science"
feng = round15-object-link-progress "Feng Yanghe" "NUDT War Skull / Bayesian-noisy-label decision science carrier" "same NUDT institution as Chen and Zhang Daibing" false "recover military-task/work-package/code identifiers and named collaborators across retained cohort" "institutional strategic mission does not create common event cause"
zhou = round15-object-link-progress "Zhou Guangyuan" "DICP DNL2200 high-performance polymer materials centre" "no literal cross-cohort programme receipt located" false "search DNL2200 grants/patents/enterprise-transfer partners against retained institutions" "post-loss centre leadership transition remains succession evidence, not cause"
liu = round15-object-link-progress "Liu Donghao" "Big Data Security Engineering Research Center / DSMM" "no literal cross-cohort programme receipt located" false "date governance/company identifiers and search shared national project/task numbers" "governance transition chronology remains distinct from event cause"
zhangXiaoxin = round15-object-link-progress "Zhang Xiaoxin" "NSMC/Fengyun space-weather programme carrier" "space/aerospace capability adjacency only" false "recover Fengyun payload/project identifiers and cross-institution participant list" "stale committee pages and posthumous publication cannot pay programme succession or cause"
zhangDaibing = round15-object-link-progress "Zhang Daibing" "NUDT UAV/autonomous landing and robotics carrier" "same NUDT institution as Chen/Feng; no common task located" false "recover exact NUDT programme/code/task number and participant roster" "event/source chronology must remain separate from autonomous-systems relevance"
liMinyong = round15-object-link-progress "Li Minyong" "photopharmacology / probe patent and Hainan-Shandong research carrier" "no literal cross-cohort programme receipt located" false "search grant/project/patent co-custody identifiers before cross-domain integration" "post-loss lab/project custody does not imply targeted disruption"
fang = round15-object-link-progress "Fang Daining" "BIT advanced-structure / metamaterial inverse-design carrier" "strategic materials adjacency only" false "recover named national project/grant and cross-institution work-package participants" "pre-loss distributed institute leadership weakens simple single-point capability-loss model"
yan = round15-object-link-progress "Yan Hong" "NPU hypersonic/thermal-plasma flow-control carrier" "strategic aerospace adjacency only" false "recover exact NPU/national project identifiers and partner institutions" "stale pre-loss committee/profile surfaces cannot pay post-loss programme linkage"

round15All : List Round15ObjectLinkProgress
round15All = nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷ thomas ∷ amy ∷ ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷ zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

round15ScientificCohortCount : Nat
round15ScientificCohortCount = 20

round15EveryScientistTouched : Bool
round15EveryScientistTouched = true

round15LiteralCommonProgrammePromotionCount : Nat
round15LiteralCommonProgrammePromotionCount = 0

round15InstitutionalAdjacencyDoesNotPayObjectLink : Bool
round15InstitutionalAdjacencyDoesNotPayObjectLink = false

round15CapabilityFitDoesNotPayEventCause : Bool
round15CapabilityFitDoesNotPayEventCause = false

round15SearchResidualCreatesKnownAbsence : Bool
round15SearchResidualCreatesKnownAbsence = false
