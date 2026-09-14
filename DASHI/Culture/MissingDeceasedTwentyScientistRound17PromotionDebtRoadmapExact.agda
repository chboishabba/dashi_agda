module DASHI.Culture.MissingDeceasedTwentyScientistRound17PromotionDebtRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ROUND 17: PROMOTION-DEBT ROADMAP
--
-- The investigation now has enough science/object coverage that the live debt
-- is not "find more thematic similarity".  The debt is promotion-specific:
-- what literal receipt would move a row from H1 -> H2, and what operational
-- evidence would then move it from H2 -> H3.  No row may skip these stages.
------------------------------------------------------------------------

data PromotionStage : Set where
  H0admissible
  H1strategicExposure
  H2sharedProgrammePaid
  H3targetingPaid : PromotionStage

record PromotionDebt : Set where
  constructor promotion-debt
  field
    person : String
    currentStage : PromotionStage
    strongestPaidObject : String
    h1ToH2Debt : String
    h2ToH3Debt : String
    currentNegativeControl : String
    paretoPriority : Nat

open PromotionDebt public

nuno = promotion-debt "Nuno F. G. Loureiro" H1strategicExposure
  "MIT PSFC / Viriato-KREHM science carrier"
  "literal grant/work-package/facility/repository receipt naming Nuno and another retained scientist on the same programme object"
  "pre-event operational action tied to that paid shared object: security/custody/access/investigative linkage"
  "fusion/plasma relevance is common across many independent programmes" 3

leblanc = promotion-debt "Joshua Kyle LeBlanc" H1strategicExposure
  "Fission Surface Power I&C WBS 658133.04.01.22.01.06"
  "post-loss TechMat roster or subordinate WBS naming another retained scientist/component on the same FSP object"
  "object-linked operational action or cross-case security/investigative identifier predating public aggregation"
  "NASA/aerospace portfolio overlap alone is expected" 2

maiwald = promotion-debt "Frank W. Maiwald" H1strategicExposure
  "JPL SURP SP23012 / action-spectroscopy project"
  "shared JPL instrument/procurement/work-package identifier naming another retained scientist"
  "pre-event action against the shared instrument/data/custody state with cross-case linkage"
  "JPL institutional overlap with Hicks is not project identity" 2

reza = promotion-debt "Monica Jacinto / Monica Reza" H1strategicExposure
  "Mondaloy lineage; later AFRL procurement FA930020P5032"
  "pre-2013 AFRL Mondaloy contract/programme-review/work-package naming Reza/Hardwick and McCasland or another retained scientist"
  "operational targeting/security/custody evidence tied to that exact paid programme object"
  "2020 Mondaloy procurement post-dates McCasland AFRL command and cannot retroactively create involvement" 1

grillmair = promotion-debt "Carl J. Grillmair" H1strategicExposure
  "Caltech/IPAC stellar-stream survey/catalogue carrier"
  "survey/catalogue/project identifier shared with another retained scientist"
  "cross-case operational action tied to that exact shared survey/data object"
  "ordinary survey collaboration and ordinary-event explanations remain strong controls" 3

hicks = promotion-debt "Michael David Hicks" H1strategicExposure
  "JPL small-body observing / 3122 Florence campaign"
  "observing-program/work-package/procurement identifier shared with another retained scientist"
  "cross-case security/custody action tied to that paid object"
  "same employer as Maiwald does not imply same project" 3

mccasland = promotion-debt "William Neil McCasland" H1strategicExposure
  "AFRL command / Space Vehicles chronology"
  "briefing, contract, review or tasking document naming McCasland on Mondaloy/Reza or another retained scientist's exact object"
  "pre-event operational action tied to the same paid object and another retained case"
  "command hierarchy is not programme participation" 1

chavez = promotion-debt "Anthony Chavez" H1strategicExposure
  "LANL DARHT/Scorpius engineering carrier, identity still gated"
  "first same-person weld; then a DARHT/Scorpius task/work-package shared with another retained scientist"
  "pre-event common operational/security identifier after identity and programme identity are both paid"
  "science cannot transfer across the missing-person identity seam" 1

thomas = promotion-debt "Jason R. Thomas" H1strategicExposure
  "Novartis signalling/ferritinophagy assay objects"
  "literal grant/consortium/platform/vendor object naming another retained scientist"
  "operational action tied to that shared object and event chronology"
  "thematic biotechnology adjacency is too broad" 4

amy = promotion-debt "Amy Eskridge" H1strategicExposure
  "HAL5 2018 explicit historical Ning Li/Torr reference; Institute gravity-modification programme"
  "Amy-authored/recorded technical object or NASA/Institute review receipt containing AC Gravity/DAAH01-01-9-R001 shared apparatus/personnel/programme identity"
  "pre-event common operational/security/custody action involving the paid shared object"
  "historical awareness/reference of Ning does not establish shared programme membership" 1

ning = promotion-debt "Ning Li" H1strategicExposure
  "DAAH01-01-9-R001 / Gravito-Electro Magnetic Superconductivity Experiment"
  "primary FY2001 row/SOW/closeout naming a second retained scientist, shared facility, subcontract, or apparatus later welded to another row"
  "pre-event operational/security/custody action tied to that same shared object"
  "a single-person programme identifier is not a cross-person link" 1

chen = promotion-debt "Chen Shuming" H1strategicExposure
  "NUDT Galaxy/Feiteng military-DSP lineage"
  "exact NUDT/national task identifier naming Chen and Feng or Zhang Daibing on one programme object"
  "pre-event operational action against that same object with cross-case linkage"
  "same strategic university does not imply same task" 2

feng = promotion-debt "Feng Yanghe" H1strategicExposure
  "NUDT War Skull / military-intelligence decision-science carrier"
  "War Skull task/code/work-package identifier naming Chen, Zhang Daibing, or another retained scientist/component"
  "pre-event operational/security/tasking action linked to that shared object"
  "shared NUDT mission is institutional, not object identity" 2

zhou = promotion-debt "Zhou Guangyuan" H1strategicExposure
  "DICP DNL2200 high-performance polymer materials centre"
  "grant/patent/enterprise-transfer identifier shared with another retained scientist/institutional object"
  "pre-event operational/custody action tied to that shared material programme"
  "post-loss centre succession is ordinary capability continuity evidence" 3

liu = promotion-debt "Liu Donghao" H1strategicExposure
  "Big Data Security Engineering Research Center / DSMM"
  "dated national project/task/company identifier shared with another retained scientist/programme"
  "pre-event operational/security case linkage tied to that shared object"
  "governance transition does not imply targeting" 4

zhangXiaoxin = promotion-debt "Zhang Xiaoxin" H1strategicExposure
  "NSMC/Fengyun space-weather programme"
  "exact Fengyun payload/project identifier with another retained scientist/component"
  "pre-event operational action tied to the same payload/project"
  "stale committee pages and posthumous publication do not pay programme-event linkage" 3

zhangDaibing = promotion-debt "Zhang Daibing" H1strategicExposure
  "NUDT UAV/autonomous-landing/robotics carrier"
  "exact NUDT unmanned-systems task/code identifier shared with Feng/Chen or another retained scientist"
  "pre-event operational/security action against that exact shared object"
  "same university and military relevance remain H1-only" 2

liMinyong = promotion-debt "Li Minyong" H1strategicExposure
  "photopharmacology / fluorescent-probe patent family"
  "grant/project/patent co-custody identifier shared with another retained scientist/programme"
  "pre-event operational/custody action tied to that exact shared object"
  "post-loss lab/project custody is not event cause" 4

fang = promotion-debt "Fang Daining" H1strategicExposure
  "BIT advanced-structure/metamaterial inverse-design carrier"
  "national project/grant/work-package naming another retained scientist or paid cross-institution object"
  "pre-event operational action tied to that exact shared project"
  "distributed pre-loss leadership weakens a simple single-point-loss explanation" 2

yan = promotion-debt "Yan Hong" H1strategicExposure
  "NPU hypersonic thermal/plasma flow-control carrier"
  "exact national/NPU project or facility identifier shared with another retained scientist/component"
  "pre-event operational/security action tied to that exact shared object"
  "strategic aerospace relevance is not programme identity" 3

round17All : List PromotionDebt
round17All = nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷ thomas ∷ amy ∷ ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷ zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

round17ScientificCohortCount : Nat
round17ScientificCohortCount = 20

round17EveryScientistTouched : Bool
round17EveryScientistTouched = true

round17H2PaidCount : Nat
round17H2PaidCount = 0

round17H3PaidCount : Nat
round17H3PaidCount = 0

h1ToH2RequiresLiteralCrossPersonProgrammeReceipt : Bool
h1ToH2RequiresLiteralCrossPersonProgrammeReceipt = true

h2ToH3RequiresOperationalTargetingEvidence : Bool
h2ToH3RequiresOperationalTargetingEvidence = true

temporalConcentrationCannotSkipH2 : Bool
temporalConcentrationCannotSkipH2 = true

scienceCoverageCannotSkipProgrammeIdentity : Bool
scienceCoverageCannotSkipProgrammeIdentity = true

currentParetoPriority : String
currentParetoPriority =
  "1: Ning primary Army SOW/closeout; Reza pre-2013 AFRL Mondaloy programme records; Amy technical/release object; Chavez identity weld. 2: NUDT shared task IDs and LeBlanc FSP partner/WBS surfaces. 3: JPL shared work packages and Chinese national-project/facility IDs. Only after H2 is paid should event chronology be tested for H3 operational linkage."
