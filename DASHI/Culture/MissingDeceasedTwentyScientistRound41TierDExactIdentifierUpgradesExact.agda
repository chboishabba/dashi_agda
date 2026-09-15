module DASHI.Culture.MissingDeceasedTwentyScientistRound41TierDExactIdentifierUpgradesExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistRound40CohortFrontierRefreshExact as R40

record ExactIdentifierUpgrade : Set where
  constructor exact-identifier-upgrade
  field
    person : String
    priorFrontier : String
    exactIdentifier : String
    sourceBoundary : String
    exactIdentifierPaid : Bool
    secondRetainedPersonOnSameIdentifierPaid : Bool
    H2Paid : Bool
    nextLeaf : String

open ExactIdentifierUpgrade public

jasonThomasUpgrade : ExactIdentifierUpgrade
jasonThomasUpgrade = exact-identifier-upgrade
  "Jason R. Thomas"
  "Novartis chemical-biology / ferritinophagy and signalling objects"
  "NIH U54-HL127365 on a Novartis/Harvard STING-IRF3/NFkB chemical-biology project surface naming Jason R. Thomas"
  "The ACS project/grant surface pays Thomas's participation and the grant identifier only; it does not place another retained scientist on that project or transfer claims from separate ferritinophagy work."
  true false false
  "snowball U54-HL127365 and Thomas's exact Novartis platform/project records for a second retained-person crossing identifier"

liMinyongUpgrade : ExactIdentifierUpgrade
liMinyongUpgrade = exact-identifier-upgrade
  "Li Minyong"
  "photopharmacology / fluorescent-probe patent family"
  "CN201110101082.5; CN201110100874.0; CN201110100999.3; CN201210030683.6; CN201210030393.1"
  "Shandong University institutional profile pays the listed patent filings and named co-inventor surface; a patent family is not automatically a cross-cohort programme."
  true false false
  "snowball these patent numbers, assignees, inventors and grant acknowledgements for a literal retained-person shared object"

yanHongUpgrade : ExactIdentifierUpgrade
yanHongUpgrade = exact-identifier-upgrade
  "Yan Hong"
  "NPU hypersonic/plasma flow-control carrier"
  "National Natural Science Foundation of China project 51176157"
  "The 2015 surface-discharge shock-control paper pays Yan Hong's authorship, NPU affiliation and NSFC project identifier; it does not name another retained scientist."
  true false false
  "snowball 51176157 into project outputs, team rosters, facilities and related national-programme identifiers"

liuDonghaoUpgrade : ExactIdentifierUpgrade
liuDonghaoUpgrade = exact-identifier-upgrade
  "Liu Donghao"
  "Guizhou Big Data Security Engineering Research Center / DSMM"
  "public DSMM data-security governance conference role surface"
  "The conference programme pays Liu Donghao's Deputy Director / CEO organisational role and DSMM presentation identity; it does not pay a national task, grant or project identifier."
  false false false
  "acquire the dated DSMM/national project, standardisation task, company contract or engineering-centre project identifier behind the governance work"

jasonThomasGrantIdentifierPaid : Bool
jasonThomasGrantIdentifierPaid = true

liMinyongPatentIdentifiersPaid : Bool
liMinyongPatentIdentifiersPaid = true

yanHongGrantIdentifierPaid : Bool
yanHongGrantIdentifierPaid = true

liuDonghaoRoleSurfacePaid : Bool
liuDonghaoRoleSurfacePaid = true

liuDonghaoExactTaskIdentifierPaid : Bool
liuDonghaoExactTaskIdentifierPaid = false

exactIdentifierWithoutSecondRetainedPersonDoesNotPayH2 : Bool
exactIdentifierWithoutSecondRetainedPersonDoesNotPayH2 = true

separateSourceSurfacesDoNotTransferProjectMembership : Bool
separateSourceSurfacesDoNotTransferProjectMembership = true

round41UpgradeCount : Nat
round41UpgradeCount = 4

round41H2PaidCount : Nat
round41H2PaidCount = 0

round41H3PaidCount : Nat
round41H3PaidCount = 0

round41Pareto : String
round41Pareto = "Tier-D refresh paid exact identifiers for Jason Thomas, Li Minyong and Yan Hong, and a stronger organisational role surface for Liu Donghao. Next search should use U54-HL127365, the listed CN patent numbers, NSFC 51176157, and the DSMM engineering-centre role as literal snowball keys. None pays H2 without a second retained scientist on the same exact object."
