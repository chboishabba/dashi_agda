module DASHI.Culture.MissingDeceasedTwentyScientistRound52TwentyPersonOperationalFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistRound51SensibLawPNFClaimMatrixExact as R51
import DASHI.Culture.MissingDeceasedTwentyScientistRound40CohortFrontierRefreshExact as R40
import DASHI.Culture.MissingDeceasedTwentyScientistRound41TierDExactIdentifierUpgradesExact as R41

------------------------------------------------------------------------
-- ROUND 52: TWENTY-PERSON OPERATIONAL FRONTIER
--
-- Every retained person receives one compact operational row.  The row is not
-- a biography.  It exposes the strongest paid fact, the live proposition that
-- remains decision-relevant, the promotion-critical residual, and the three
-- professional consumer projections inherited from R50/R51.
------------------------------------------------------------------------

data OperationalClass : Set where
  paidFact : OperationalClass
  liveDisputedProposition : OperationalClass
  promotionCriticalResidual : OperationalClass

record ConsumerProjection : Set where
  constructor consumer-projection
  field
    investigatorView : String
    lawyerView : String
    journalistView : String

open ConsumerProjection public

record TwentyPersonOperationalRow : Set where
  constructor twenty-person-operational-row
  field
    person : String
    strongestPaidCarrier : String
    paidFactReference : String
    liveProposition : String
    operationalClass : OperationalClass
    promotionCriticalResidualReference : String
    nextDiscriminatingAcquisition : String
    consumerProjection : ConsumerProjection
    h2Paid : Bool
    h3Paid : Bool

open TwentyPersonOperationalRow public

mkProjection : String → String → String → ConsumerProjection
mkProjection = consumer-projection

nuno : TwentyPersonOperationalRow
nuno = twenty-person-operational-row
  "Nuno F. G. Loureiro"
  "PRACE VIRIATO project/resource allocation and collaborator surface"
  "R40: exact VIRIATO/HPC carrier paid"
  "another retained scientist appears on the same literal VIRIATO/grant/facility/repository object"
  promotionCriticalResidual
  "retained-person same-object identity"
  "snowball VIRIATO project/resource identifiers, repository metadata and collaborator/facility records"
  (mkProjection "search exact project/resource identifiers" "treat project membership as proposition-specific; no causal/legal inference" "publish exact project role, not a common-programme claim")
  false false

leblanc : TwentyPersonOperationalRow
leblanc = twenty-person-operational-row
  "Joshua Kyle LeBlanc"
  "NASA FSP/FICS WBS 658133.04.01.22.01.06 team surface"
  "R40: exact WBS/team carrier paid"
  "a retained scientist crosses a subordinate FSP component/vendor/review/work-package object"
  promotionCriticalResidual
  "second retained person on exact subordinate object"
  "snowball WBS children, component reviews, partner/vendor records and named team products"
  (mkProjection "search subordinate WBS/components" "preserve WBS membership versus downstream proposition purpose" "state named NASA role; do not infer broader linkage")
  false false

maiwald : TwentyPersonOperationalRow
maiwald = twenty-person-operational-row
  "Frank W. Maiwald"
  "JPL SURP SP23012 PI/co-investigator apparatus and publication surface"
  "R40: SP23012 exact carrier paid"
  "another retained scientist shares SP23012 instrument/procurement/work-package identity"
  promotionCriticalResidual
  "retained crossing on exact JPL object"
  "snowball SP23012 procurement, instrument, facility and publication identifiers"
  (mkProjection "search apparatus/procurement crossings" "authenticate exact JPL carrier separately from any downstream claim" "publish exact project facts only")
  false false

reza : TwentyPersonOperationalRow
reza = twenty-person-operational-row
  "Monica Jacinto / Monica Reza"
  "Mondaloy Development for Hydrocarbon Boost Technology Demonstrator + FA9300-07-C-0001 context"
  "R31-R39: Monica exact HCB/Mondaloy role paid"
  "Monica and McCasland were on the same exact HCB/Mondaloy task/object"
  promotionCriticalResidual
  "identity-bearing McCasland same-object receipt"
  "acquire 2011-2013 HCB task/modification/review/roster/materials-approval record naming McCasland"
  (mkProjection "highest-alpha H2 leaf" "role surfaces remain distinct; no wrongdoing/causation proposition" "may report unresolved same-object question only with cross-granularity caveat")
  false false

grillmair : TwentyPersonOperationalRow
grillmair = twenty-person-operational-row
  "Carl J. Grillmair"
  "IPAC/Spitzer/Palomar stellar-stream project surfaces"
  "R40: concrete stream/project carriers paid"
  "a retained scientist shares an exact survey/catalog/project/facility identifier"
  promotionCriticalResidual
  "literal retained crossing"
  "snowball survey IDs, observing programmes, instrument/team records and acknowledgments"
  (mkProjection "search exact survey/facility IDs" "keep publication authorship separate from legal/causal propositions" "publish project specifics; no cluster inference")
  false false

hicks : TwentyPersonOperationalRow
hicks = twenty-person-operational-row
  "Michael David Hicks"
  "JPL/CNEOS 3122 Florence observing campaign"
  "R40: exact campaign/team/facility surface paid"
  "another retained scientist shares the exact Florence observing programme/instrument/work package"
  promotionCriticalResidual
  "retained crossing on exact observing object"
  "snowball observation IDs, telescope programmes, schedules and instrument records"
  (mkProjection "search exact observing programme" "campaign participation does not pay other allegations" "publish named campaign/team only")
  false false

mccasland : TwentyPersonOperationalRow
mccasland = twenty-person-operational-row
  "William Neil McCasland"
  "personal public HCB programme reference"
  "R34-R39: personal HCB reference paid"
  "McCasland had an exact 2011-2013 task/contract/Mondaloy role on Monica's HCB object"
  promotionCriticalResidual
  "exact contemporaneous role receipt"
  "search HCB reviews, attendee/distribution records, contract mods, approvals and proceedings"
  (mkProjection "highest-alpha H2 leaf paired with Reza" "programme reference is not exact task participation" "report programme reference separately from same-task claim")
  false false

chavez : TwentyPersonOperationalRow
chavez = twenty-person-operational-row
  "Anthony Chavez"
  "LANL DARHT career + Scorpius accelerator design work"
  "R40: identity and Scorpius/DARHT role paid"
  "another retained scientist appears on the same Scorpius/DARHT task/drawing/review/facility object"
  promotionCriticalResidual
  "retained-person shared engineering object"
  "snowball Scorpius design reviews, beamline/work-package/drawing and NNSS-LANL team records"
  (mkProjection "search exact engineering artefacts" "same facility/programme is not same task or causal link" "publish LANL-paid role; avoid extending beyond named work")
  false false

thomas : TwentyPersonOperationalRow
thomas = twenty-person-operational-row
  "Jason R. Thomas"
  "Novartis chemical-biology project with NIH U54-HL127365"
  "R41: exact grant identifier paid"
  "another retained scientist appears on U54-HL127365 or same exact Novartis platform/project"
  promotionCriticalResidual
  "retained crossing on exact grant/platform"
  "snowball U54-HL127365 consortium personnel, publications, grant records and Novartis project surfaces"
  (mkProjection "search grant roster and exact platform IDs" "separate grant project from other Thomas publications" "publish grant attribution without merging distinct projects")
  false false

amy : TwentyPersonOperationalRow
amy = twenty-person-operational-row
  "Amy Eskridge"
  "HAL5/Amy-team surface + candidate NASA MSFC POAMS object + archived 2020 statement"
  "R28-R30: compatibility and archived statement carrier paid; exact referent identity unpaid"
  "Amy's statement identifies the candidate NASA paper/review object or another retained scientist"
  liveDisputedProposition
  "same-object referent identity"
  "acquire authenticated Amy original, NASA public-release/review metadata or identity-bearing correspondence"
  (mkProjection "continue referent backtrace" "archived screenshot/statement authenticity and proposition scope remain separate" "attribute statement; do not state exact NASA-paper identity as established")
  false false

ning : TwentyPersonOperationalRow
ning = twenty-person-operational-row
  "Ning Li"
  "Army FY2001 award DAAH01-01-9-R001 locator"
  "R26: official locator paid; primary SOW/closeout bytes unpaid"
  "the award's primary technical object/personnel surface crosses another retained scientist"
  promotionCriticalResidual
  "primary bytes + retained crossing"
  "obtain primary SOW/closeout/award file; enumerate personnel, facilities, subcontractors and apparatus"
  (mkProjection "primary-document acquisition first" "locator does not authenticate unseen contents" "report award locator and unresolved primary record status")
  false false

chen : TwentyPersonOperationalRow
chen = twenty-person-operational-row
  "Chen Shuming"
  "NUDT Galaxy/Feiteng military chip/DSP lineage"
  "R27: exact object family paid"
  "a literal NUDT task/project/codebase identifier crosses another retained scientist"
  promotionCriticalResidual
  "same exact NUDT object"
  "snowball project numbers, lab task IDs, chip/programme acknowledgments and co-project personnel"
  (mkProjection "search literal NUDT identifiers" "institution membership cannot pay same-task proposition" "publish exact object family, not hidden common programme")
  false false

feng : TwentyPersonOperationalRow
feng = twenty-person-operational-row
  "Feng Yanghe"
  "NUDT patent CN112861442B on deep-RL multi-aircraft collaborative air-combat planning"
  "R27: exact patent/object paid"
  "another retained scientist appears on the same patent/task/project lineage"
  promotionCriticalResidual
  "retained crossing on exact object"
  "snowball patent family, assignee records, project acknowledgments and related NUDT task IDs"
  (mkProjection "search exact patent/project lineage" "patent assignee/inventor roles are proposition-specific" "publish patent facts without generalising to unrelated NUDT work")
  false false

zhou : TwentyPersonOperationalRow
zhou = twenty-person-operational-row
  "Zhou Guangyuan"
  "DICP DNL2200 high-performance polymer materials centre surface"
  "R40: exact institutional technical carrier paid"
  "an exact grant/patent/transfer identifier crosses another retained scientist"
  promotionCriticalResidual
  "exact transfer/project identifier"
  "snowball DNL2200 grants, patents, enterprise-transfer records and named project teams"
  (mkProjection "search grant/patent/transfer IDs" "centre affiliation does not determine same project" "publish centre role with source-bounded wording")
  false false

liu : TwentyPersonOperationalRow
liu = twenty-person-operational-row
  "Liu Donghao"
  "Guizhou Big Data Security Engineering Research Center leadership + DSMM governance presentation"
  "R41: role/presentation surface paid; exact task identifier unpaid"
  "a specific DSMM/national project/standardisation/contract object can be identified and crossed"
  promotionCriticalResidual
  "exact task/grant/project identifier"
  "acquire engineering-centre project IDs, DSMM standardisation tasks, contracts or national-project records"
  (mkProjection "resolve exact task ID before crossing search" "organisational role is not a specific project receipt" "attribute role/presentation; avoid implying hidden task")
  false false

zhangXiaoxin : TwentyPersonOperationalRow
zhangXiaoxin = twenty-person-operational-row
  "Zhang Xiaoxin"
  "Fengyun-4C far-ultraviolet ionospheric retrieval paper/team/contribution surface"
  "R40: exact Fengyun technical object paid"
  "another retained scientist shares an exact payload/instrument/project/funding/operations identifier"
  promotionCriticalResidual
  "retained crossing on payload/project ID"
  "snowball Fengyun payload, FYSIC/NSMC, funding and operations identifiers"
  (mkProjection "search payload/project identifiers" "paper authorship/contribution does not pay unrelated programme membership" "publish exact contribution with payload context")
  false false

zhangDaibing : TwentyPersonOperationalRow
zhangDaibing = twenty-person-operational-row
  "Zhang Daibing"
  "2018 NUDT UAV landing paper DOI 10.11887/j.cn.201801023"
  "R27: exact publication/object family paid"
  "a literal project/task/platform identifier crosses another retained scientist"
  promotionCriticalResidual
  "same exact NUDT task/platform"
  "snowball funding acknowledgments, UAV platform IDs, lab/team records and project numbers"
  (mkProjection "search exact project/platform" "co-institution status is insufficient" "publish paper/object facts only")
  false false

liMinyong : TwentyPersonOperationalRow
liMinyong = twenty-person-operational-row
  "Li Minyong"
  "five exact Shandong University CN patent filings"
  "R41: exact patent identifiers and named co-inventors paid"
  "a retained scientist appears in the same patent/grant/project family"
  promotionCriticalResidual
  "retained crossing on patent/grant object"
  "snowball patent families, assignees, grant acknowledgments and co-inventor project records"
  (mkProjection "search exact patent/grant roots" "patent listing supports inventor/object proposition only" "publish patent identifiers and co-inventors without overreach")
  false false

fang : TwentyPersonOperationalRow
fang = twenty-person-operational-row
  "Fang Daining"
  "2024 inverse-design phononic meta-structured materials publication/team"
  "R40: exact publication/team surface paid"
  "an exact national project/grant/work-package crosses another retained scientist"
  promotionCriticalResidual
  "grant/project retained crossing"
  "snowball funding acknowledgments, national project numbers, lab/facility and co-project records"
  (mkProjection "search project/grant acknowledgments" "technical importance does not pay causation/targeting" "publish exact paper/team and locally sourced event facts")
  false false

yan : TwentyPersonOperationalRow
yan = twenty-person-operational-row
  "Yan Hong"
  "hypersonic/plasma-flow-control paper with NSFC 51176157"
  "R41: exact grant identifier paid"
  "another retained scientist appears on NSFC 51176157 or an exact linked project/facility object"
  promotionCriticalResidual
  "retained crossing on grant/project"
  "snowball 51176157 outputs, team records, facilities and National Numerical Wind Tunnel linkage"
  (mkProjection "search grant outputs/team" "grant membership is source- and period-specific" "publish exact grant/project facts; do not infer targeting")
  false false

round52Rows : List TwentyPersonOperationalRow
round52Rows =
  nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷ thomas ∷ amy ∷
  ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷ zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

round52RetainedCount : Nat
round52RetainedCount = 20

-- Each row contains at least one already-paid carrier/fact surface.  The class
-- below counts rows whose *current decision* is satisfied without further
-- promotion.  None of the H2/H3 decisions are in that state, so the operational
-- frontier is dominated by residual work rather than closed rows.
round52PaidFactCount : Nat
round52PaidFactCount = 20

round52LiveDisputedCount : Nat
round52LiveDisputedCount = 1

round52PromotionCriticalCount : Nat
round52PromotionCriticalCount = 19

allTwentyCarryVisibleResidual : Bool
allTwentyCarryVisibleResidual = true

consumerProjectionCannotPromoteBaseClass : Bool
consumerProjectionCannotPromoteBaseClass = true

paidFactDoesNotErasePromotionDebt : Bool
paidFactDoesNotErasePromotionDebt = true

sameInstitutionCannotUpgradePromotionClass : Bool
sameInstitutionCannotUpgradePromotionClass = true

sameProgrammeCannotUpgradeToSameObjectWithoutReceipt : Bool
sameProgrammeCannotUpgradeToSameObjectWithoutReceipt = true

legalOrPublicationConsumerCannotPayH2 : Bool
legalOrPublicationConsumerCannotPayH2 = true

legalOrPublicationConsumerCannotPayH3 : Bool
legalOrPublicationConsumerCannotPayH3 = true

round52H2PaidCount : Nat
round52H2PaidCount = 0

round52H3PaidCount : Nat
round52H3PaidCount = 0

round52Reading : String
round52Reading = "The whole retained twenty is now operational rather than biographical. Every row exposes the strongest already-paid carrier, the current decision-relevant proposition, a visible promotion-critical residual, the next discriminating acquisition, and investigator/lawyer/journalist projections. Twenty rows have at least one paid factual carrier, nineteen current decisions are promotion-critical residuals, and Amy's exact referent weld remains a live disputed proposition. Consumer-specific treatment cannot upgrade the base evidentiary class. H2 and H3 remain zero."

round52Pareto : String
round52Pareto = "Prioritise rows by expected ability of one acquisition to change H2/H3 or collapse a major provenance uncertainty. Tier A remains Reza/McCasland exact HCB same-object receipt. Tier B remains Ning primary award bytes, Amy exact referent/NASA review weld and Chavez exact Scorpius/DARHT engineering crossings. Tier C is LeBlanc/JPL/NUDT exact identifier crossing. Tier D continues exact grant/patent/project snowballs. Do not spend acquisition effort on adding more narrative repetition where the residual is already precisely typed."
