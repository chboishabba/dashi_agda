module DASHI.Culture.AmyEskridgeVideoUS11PriorArtReconciliationExact where

-- SOURCE-EXACT RECONCILIATION OF THE TWO **ELEVEN** DENOMINATORS.
-- NO new roster constructed from a count. Source objects imported directly.
--
-- Producer owners:
-- DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinProgressExact.agda
--   U.S. scientific *research* denominator 11, China 9; primary technical
--   sources and per-person residuals developed over many investigation rounds.
-- DASHI/Culture/MissingDeceasedTwentyScientistRound44OfficialInquiryCohortExact.agda
--   Ten-person public-reporting reconstruction, only part directly
--   named in Congress' April 20 2026 letter.
-- DASHI/Culture/AmyEskridgeVideoEleventhMediaRosterWeldExact.agda
--   Source-welded Fox 11-person *media* roster, article April 17 2026:
-- https://www.foxnews.com/politics/11th-scientist-death-emerges-string-missing-dead-officials-access-us-secrets/
-- Crucially these 11-person sets are not the same: intersection 9,
-- researcher-only LeBlanc and Ning Li, Fox-only Casias and Garcia.
-- Roster membership DOES NOT independently certify research role, security
-- clearance, identity weld for Anthony Chavez, murder or a shared operation.
-- The 2022 Amy event predates the House 2023-onward case window.
-- Attribution: Docs/SourceAttributionPolicy.md.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Culture.MissingDeceasedTwentyScientistRoundRobinProgressExact as Research
import DASHI.Culture.MissingDeceasedTwentyScientistRound44OfficialInquiryCohortExact as House
import DASHI.Culture.MissingDeceasedRosterRoleAndCommitteeWeldAuditExact as Role
import DASHI.Culture.AmyEskridgeVideoEleventhMediaRosterWeldExact as Fox
import DASHI.Culture.MissingDeceasedTwentyScientistRound68HCBDOITechnicalLineageExact as HCB
import DASHI.Culture.MissingDeceasedTwentyScientistRound70HCBTaskLevelBoundedExhaustionExact as HCB70
import DASHI.Culture.MissingDeceasedTwentyScientistRound75POAMSSpaceActSubagreementExact as POAMS75
import DASHI.Culture.MissingDeceasedTwentyScientistRound77POAMSNamedPrivateSponsorExact as POAMS77
import DASHI.Culture.MissingDeceasedTwentyScientistRound79AmyPOAMSTransferBoundedExhaustionExact as POAMS79
import DASHI.Culture.MissingDeceasedTwentyScientistRound83LeBlancExactWBSRetainedSweepExact as LeBlanc83
import DASHI.Culture.MissingDeceasedTwentyScientistRound85NingFOIAProceduralClosureExact as Ning85
import DASHI.Culture.MissingDeceasedTwentyScientistRound86NingDODOIGFOIALogBoundaryExact as Ning86
import DASHI.Culture.MissingDeceasedTwentyScientistRound88NingAMCOMPrimaryAcquisitionContractExact as Ning88

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

append : {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

researchUS11 : List Research.ScientistRoundProgress
researchUS11 =
  Research.nunoLoureiroRound ∷
  Research.joshuaLeBlancRound ∷
  Research.frankMaiwaldRound ∷
  Research.monicaRezaRound ∷
  Research.carlGrillmairRound ∷
  Research.michaelHicksRound ∷
  Research.neilMcCaslandRound ∷
  Research.anthonyChavezRound ∷
  Research.jasonThomasRound ∷
  Research.amyEskridgeRound ∷
  Research.ningLiRound ∷ []

researchChina9 : List Research.ScientistRoundProgress
researchChina9 =
  Research.chenShumingRound ∷
  Research.fengYangheRound ∷
  Research.zhouGuangyuanRound ∷
  Research.liuDonghaoRound ∷
  Research.zhangXiaoxinRound ∷
  Research.zhangDaibingRound ∷
  Research.liMinyongRound ∷
  Research.fangDainingRound ∷
  Research.yanHongRound ∷ []

researchUSCount : length researchUS11 ≡ 11
researchUSCount = refl

researchChinaCount : length researchChina9 ≡ 9
researchChinaCount = refl

entireExistingResearchCohort :
  append researchUS11 researchChina9 ≡ Research.twentyScientistRoundProgress
entireExistingResearchCohort = refl

researchDeclaredUSCount : Research.usScientificCohortCount ≡ 11
researchDeclaredUSCount = refl

researchDeclaredChinaCount : Research.chineseScientificCohortCount ≡ 9
researchDeclaredChinaCount = refl

foxMedia11 : List Fox.SecondaryReportedRosterMember
foxMedia11 = Fox.foxPublishedNamesNormalized

mediaElevenCount : length foxMedia11 ≡ 11
mediaElevenCount = refl

-- These are precise source-object joins, not an implicit name matcher.
record MediaResearchSameName : Set where
  constructor paired-name
  field
    researcher : Research.ScientistRoundProgress
    mediaMember : Fox.SecondaryReportedRosterMember
    identityAndRoleBoundary : String
open MediaResearchSameName public

nuno : MediaResearchSameName
nuno = paired-name Research.nunoLoureiroRound Fox.nuno
  "Two producer lists refer to the same named historical figure; this does not pay common programme or harm cause"

maiwald : MediaResearchSameName
maiwald = paired-name Research.frankMaiwaldRound Fox.maiwald
  "Two producer lists refer to the same named historical figure; this does not pay common programme or harm cause"

reza : MediaResearchSameName
reza = paired-name Research.monicaRezaRound Fox.reza
  "Two producer lists refer to the same named historical figure; this does not pay common programme or harm cause"

grillmair : MediaResearchSameName
grillmair = paired-name Research.carlGrillmairRound Fox.grillmair
  "Two producer lists refer to the same named historical figure; this does not pay common programme or harm cause"

hicks : MediaResearchSameName
hicks = paired-name Research.michaelHicksRound Fox.hicks
  "Two producer lists refer to the same named historical figure; this does not pay common programme or harm cause"

mccasland : MediaResearchSameName
mccasland = paired-name Research.neilMcCaslandRound Fox.mccasland
  "Two producer lists refer to the same named historical figure; this does not pay common programme or harm cause"

chavez : MediaResearchSameName
chavez = paired-name Research.anthonyChavezRound Fox.chavez
  "Shared name in two research/media collections; missing Anthony Chavez ≠ published Mark Anthony Chavez until a primary same-person receipt is obtained"

thomas : MediaResearchSameName
thomas = paired-name Research.jasonThomasRound Fox.thomas
  "Two producer lists refer to the same named historical figure; this does not pay common programme or harm cause"

amy : MediaResearchSameName
amy = paired-name Research.amyEskridgeRound Fox.amy
  "Two producer lists refer to the same named historical figure; this does not pay common programme or harm cause"

mediaResearchNine : List MediaResearchSameName
mediaResearchNine =
  nuno ∷
  maiwald ∷
  reza ∷
  grillmair ∷
  hicks ∷
  mccasland ∷
  chavez ∷
  thomas ∷
  amy ∷ []

nineNamedOverlaps : length mediaResearchNine ≡ 9
nineNamedOverlaps = refl

researchOnlyTwo : List Research.ScientistRoundProgress
researchOnlyTwo =
  Research.joshuaLeBlancRound ∷ Research.ningLiRound ∷ []

foxOnlyTwo : List Fox.SecondaryReportedRosterMember
foxOnlyTwo =
  Fox.casias ∷ Fox.garcia ∷ []

researchOnlyCount : length researchOnlyTwo ≡ 2
researchOnlyCount = refl

mediaOnlyCount : length foxOnlyTwo ≡ 2
mediaOnlyCount = refl

-- Cardinality arithmetic verifies the enumeration, NOT the factual status
-- of each role, event, shared programme, or the name collision for Chavez.
intersectionPlusResearchOnly : 9 + 2 ≡ Research.usScientificCohortCount
intersectionPlusResearchOnly = refl

intersectionPlusMediaOnly : 9 + 2 ≡ 11
intersectionPlusMediaOnly = refl

researchMediaUnionCount : Nat
researchMediaUnionCount = 9 + 2 + 2

distinctNamesAcrossBothDenominators : researchMediaUnionCount ≡ 13
distinctNamesAcrossBothDenominators = refl

houseReportingPrimaryProducer :
  Fox.houseTenProducers ≡ House.officialReportingTen
houseReportingPrimaryProducer = Fox.houseProducerListIsOriginal

casiasNonScienceRole : Role.RoleType
casiasNonScienceRole = Role.roleType Role.melissaCasiasRole

garciaNonScienceRole : Role.RoleType
garciaNonScienceRole = Role.roleType Role.stevenGarciaRole

casiasActuallyAdministrative :
  casiasNonScienceRole ≡ Role.administrativeStaff
casiasActuallyAdministrative = refl

garciaActuallyCustodial :
  garciaNonScienceRole ≡ Role.propertyCustodian
garciaActuallyCustodial = refl

-- Latest original-producer boundaries. No video source should request these
-- historical tasks afresh as though all prior source archaeology were missing.
hcbTechnicalLineagePaid : HCB.hcbRetrospectivePaysMondaloyWithinHCB ≡ true
hcbTechnicalLineagePaid = refl

hcbMcCaslandTaskReceiptStillOpen : HCB70.mccaslandTaskLevelHitLocated ≡ false
hcbMcCaslandTaskReceiptStillOpen = refl

poamsSAAOriginalFound : POAMS75.poamsFamiliarizationSubagreementPaid ≡ true
poamsSAAOriginalFound = refl

poamsNamedFunded : POAMS77.chrisMilamRequestedAndFundedEffortPaid ≡ true
poamsNamedFunded = refl

poamsAmyTransferStillOpen :
  POAMS79.explicitAmyToPOAMSInstitutionalBridgePaid ≡ false
poamsAmyTransferStillOpen = refl

leblancExactWBSRetainedHit : LeBlanc83.leblancRetainedHitPaid ≡ true
leblancExactWBSRetainedHit = refl

leblancSecondRetainedHitUnpaid : LeBlanc83.secondRetainedHitLocated ≡ false
leblancSecondRetainedHitUnpaid = refl

ningOSDFOIANotCompletedSearch :
  Ning85.foiaCompletedAgencyRecordsSearchPaid ≡ false
ningOSDFOIANotCompletedSearch = refl

ningOIGFOIARequestExists : Ning86.dodOIGRequestLogPaid ≡ true
ningOIGFOIARequestExists = refl

ningPrimaryAgreementStillUnacquired :
  Ning88.primaryAgreementInstrumentStillUnacquired ≡ true
ningPrimaryAgreementStillUnacquired = refl

ningTechnicalOutcomeUnresolved :
  Ning88.technicalOutcomeStillUnresolved ≡ true
ningTechnicalOutcomeUnresolved = refl

-- Stronger-than-appropriate promotion is not provided by these imports.
data SameNamePaysIdentityOfMissingAnthony : Set where
data AllFoxElevenAreResearchScientists : Set where
data MediaAndResearchElevenSameCohort : Set where
data ProgrammaticOverlapImpliesTargeting : Set where

noChavezIdentityCoercion : SameNamePaysIdentityOfMissingAnthony → ⊥
noChavezIdentityCoercion ()

noFoxAllScientistsCoercion : AllFoxElevenAreResearchScientists → ⊥
noFoxAllScientistsCoercion ()

noElevenDenominatorCoercion : MediaAndResearchElevenSameCohort → ⊥
noElevenDenominatorCoercion ()

noCausalityCoercion : ProgrammaticOverlapImpliesTargeting → ⊥
noCausalityCoercion ()
