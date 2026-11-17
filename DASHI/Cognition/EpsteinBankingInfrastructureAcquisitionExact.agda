module DASHI.Cognition.EpsteinBankingInfrastructureAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor

------------------------------------------------------------------------
-- BANKING / TRANSACTION INFRASTRUCTURE ACQUISITION OWNER
--
-- This owner separates institution, executive, account/transaction,
-- SAR/compliance, regulatory, civil-settlement and investigative-record surfaces.
-- Senate or media findings are attributed as such; civil settlements do not
-- create admissions; regulatory findings do not automatically establish
-- trafficking participation or criminal liability.
------------------------------------------------------------------------

data BankNode : Set where
  jpmorgan : BankNode
  deutscheBank : BankNode
  bankOfAmerica : BankNode
  bnyMellon : BankNode
  goldmanSachs : BankNode
  hsbc : BankNode

data BankingSurface : Set where
  accountRelationship : BankingSurface
  transactionFlow : BankingSurface
  cashWithdrawal : BankingSurface
  sarOrAMLReporting : BankingSurface
  executiveRelationship : BankingSurface
  eliteClientAccessBenefit : BankingSurface
  regulatoryFinding : BankingSurface
  civilSettlement : BankingSurface
  congressionalInvestigationFinding : BankingSurface
  fbi302InterviewRecord : BankingSurface

record BankingReceipt : Set where
  constructor banking-receipt
  field
    institution : BankNode
    surface : BankingSurface
    sourceClass : String
    description : String
    relationEstablished : Bool
    criminalLiabilityEstablishedByThisReceipt : Bool
    admissionEstablishedByThisReceipt : Bool
open BankingReceipt public

jpmorganSettlementReceipt : BankingReceipt
jpmorganSettlementReceipt = banking-receipt
  jpmorgan civilSettlement
  "2023 civil settlement / court record"
  "JPMorgan agreed to a USD 290m settlement of Epstein survivor claims; settlement itself does not constitute an admission of liability."
  true false false

deutscheRegulatoryReceipt : BankingReceipt
deutscheRegulatoryReceipt = banking-receipt
  deutscheBank regulatoryFinding
  "New York Department of Financial Services 2020 consent-order reporting"
  "DFS imposed a USD 150m penalty covering compliance failures including Deutsche Bank's relationship with Epstein."
  true false false

bankOfAmericaSettlementReceipt : BankingReceipt
bankOfAmericaSettlementReceipt = banking-receipt
  bankOfAmerica civilSettlement
  "2026 Reuters / civil settlement"
  "Bank of America agreed to pay USD 72.5m to settle survivor claims while denying wrongdoing; court approval remained required at reporting time."
  true false false

senateJPMorganReceipt : BankingReceipt
senateJPMorganReceipt = banking-receipt
  jpmorgan congressionalInvestigationFinding
  "Senate Finance Committee 2026 follow-the-money report"
  "Senate Finance alleges delayed screening/reporting of Epstein suspicious activity and broader failures that enabled ready access to funds."
  true false false

senateDeutscheReceipt : BankingReceipt
senateDeutscheReceipt = banking-receipt
  deutscheBank congressionalInvestigationFinding
  "Senate Finance Committee 2026 follow-the-money report"
  "Senate Finance alleges delayed/non-timely reporting of substantial suspicious Epstein transactions."
  true false false

senateBOAReceipt : BankingReceipt
senateBOAReceipt = banking-receipt
  bankOfAmerica congressionalInvestigationFinding
  "Senate Finance Committee 2026 follow-the-money report"
  "Senate Finance alleges failures to timely screen/report large transfers including Leon Black->Epstein payments."
  true false false

senateEliteAccessBenefitReceipt : BankingReceipt
senateEliteAccessBenefitReceipt = banking-receipt
  jpmorgan eliteClientAccessBenefit
  "Senate Finance Committee 2026 follow-the-money report"
  "Senate Finance attributes to top bank officials a benefit mechanism in which Epstein was protected in order to gain access to Leon Black and other billionaires. This is an attributed congressional investigative finding, not a universal motive finding for every banker or transaction."
  true false false

bnyMellonProbeReceipt : BankingReceipt
bnyMellonProbeReceipt = banking-receipt
  bnyMellon congressionalInvestigationFinding
  "Senate Finance Committee 2026-01-15 investigative request"
  "Senate Finance opened a BNY Mellon probe concerning hundreds of suspicious Epstein-related transactions and requested records including cash withdrawals above USD 10,000 from Epstein accounts between 2001 and 2019. This pays an investigative transaction/cash-withdrawal acquisition surface, not a completed finding of illegality."
  true false false

banker302Receipt : BankingReceipt
banker302Receipt = banking-receipt
  jpmorgan fbi302InterviewRecord
  "Senate Finance Committee 2026-09-30 letter to DOJ/FBI"
  "Senate Finance says its investigators discovered at least one FBI 302 documenting an interview with a banker closely tied to Epstein and demanded all Epstein-related 302s, including interviews with JPMorgan, Deutsche Bank and Bank of America employees. The existence of at least one report is paid; its contents and the identities/status of all requested banker interviews remain acquisition debts."
  true false false

record FinanceFrontStatus : Set where
  constructor finance-front-status
  field
    senateReportsAtLeast1Point4BQuestionable : Bool
    jpmorganSettlement290m : Bool
    deutscheDFS150mPenalty : Bool
    bankOfAmericaSettlement725m : Bool
    bnyMellonExplicitProbe : Bool
    banker302ExistencePaid : Bool
    eliteClientAccessBenefitAllegedBySenate : Bool
    executiveLevelExpansionRequired : Bool
    transactionLevelExpansionRequired : Bool
    sarLevelExpansionRequired : Bool
    bankFrontCurrentlyHighestGlobalAcquisitionValue : Bool
open FinanceFrontStatus public

currentFinanceFrontStatus : FinanceFrontStatus
currentFinanceFrontStatus = finance-front-status
  true true true true true true true true true true true

------------------------------------------------------------------------
-- ATTRIBUTION / PROMOTION FIREWALLS
------------------------------------------------------------------------

data SenateFindingImpliesCriminalConviction : Set where
data SettlementImpliesAdmission : Set where
data RegulatoryFindingImpliesTraffickingParticipation : Set where
data BankRelationshipImpliesExecutiveKnowledge : Set where
data SuspiciousTransactionImpliesUnderlyingCrimeProved : Set where
data InvestigativeRequestImpliesCompletedFinding : Set where
data AccessBenefitImpliesUniversalBankerMotive : Set where
data FBI302ExistenceImpliesInterviewContent : Set where

senateFindingDoesNotCreateConviction : SenateFindingImpliesCriminalConviction → ⊥
senateFindingDoesNotCreateConviction ()

settlementDoesNotCreateAdmission : SettlementImpliesAdmission → ⊥
settlementDoesNotCreateAdmission ()

regulatoryFindingDoesNotCreateTraffickingParticipation :
  RegulatoryFindingImpliesTraffickingParticipation → ⊥
regulatoryFindingDoesNotCreateTraffickingParticipation ()

bankRelationshipDoesNotCreateExecutiveKnowledge : BankRelationshipImpliesExecutiveKnowledge → ⊥
bankRelationshipDoesNotCreateExecutiveKnowledge ()

suspiciousTransactionDoesNotCreateUnderlyingCrimeProof :
  SuspiciousTransactionImpliesUnderlyingCrimeProved → ⊥
suspiciousTransactionDoesNotCreateUnderlyingCrimeProof ()

investigativeRequestDoesNotCreateCompletedFinding : InvestigativeRequestImpliesCompletedFinding → ⊥
investigativeRequestDoesNotCreateCompletedFinding ()

accessBenefitDoesNotCreateUniversalBankerMotive : AccessBenefitImpliesUniversalBankerMotive → ⊥
accessBenefitDoesNotCreateUniversalBankerMotive ()

fbi302ExistenceDoesNotCreateInterviewContent : FBI302ExistenceImpliesInterviewContent → ⊥
fbi302ExistenceDoesNotCreateInterviewContent ()


------------------------------------------------------------------------
-- 2015 OCDETF "CHAIN REACTION" SOURCE-ROOT ADAPTER
-- Distinguish an original lead-only intelligence memo, a third-party text
-- extraction, and a Senate interpretation of it. No reidentification of
-- redacted targets, no transaction credentials or raw financial reports.
------------------------------------------------------------------------

data ChainReactionSourceRole : Set where
  federalIntelligenceLeadProduct : ChainReactionSourceRole
  derivativePublicTranscriptIndex : ChainReactionSourceRole
  laterSenateInquiryInterpretation : ChainReactionSourceRole

record ChainReactionSourceReceipt : Set where
  constructor chain-reaction-source-receipt
  field
    chainReactionRole : ChainReactionSourceRole
    chainReactionLocator : String
    chainReactionEventDate : String
    chainReactionPublicationDate : String
    chainReactionScopedClaim : String
    chainReactionDocumentIdentifierLocated : Bool
    chainReactionNativeScanVerifiedHere : Bool  -- native federal memo scan, not Senate HTML correspondence
    chainReactionCriminalFindingPaid : Bool
open ChainReactionSourceReceipt public

chainReaction2015Memo : ChainReactionSourceReceipt
chainReaction2015Memo = chain-reaction-source-receipt
  federalIntelligenceLeadProduct
  "DOJ Dataset 9 EFTA00173953; May 18 2015 OFC-TP-15-12392 / SODOFC-15-12392; OCDETF NY-NYS-0829; public original access age-gated"
  "2015-05-18" "2026 DOJ disclosure"
  "Index and text identify an OCDETF multi-database Target Profile for operation Chain Reaction. Its own warning labels it a lead product, not a finished investigation or evidentiary finding; the full original scan is not verified in this source-writing pass."
  true false false

chainReactionThirdPartyIndex : ChainReactionSourceReceipt
chainReactionThirdPartyIndex = chain-reaction-source-receipt
  derivativePublicTranscriptIndex
  "https://tommycarstensen.com/epstein/data/documents/set9/00173/EFTA00173953.html"
  "2015-05-18" "third-party index current 2026"
  "Public OCR/extracted rendition of the same DOJ EFTA document, not a second OCDETF investigator or independent transaction witness. Extraction contains errors; do not promote redacted names or parsed currency strings."
  true false false

chainReactionWyden2026Questions : ChainReactionSourceReceipt
chainReactionWyden2026Questions = chain-reaction-source-receipt
  laterSenateInquiryInterpretation
  "https://www.finance.senate.gov/ranking-members-news/wyden-questions-dea-over-mystery-epstein-investigation"
  "2026-02-25" "2026-02-26"
  "Wyden asks DEA for the unredacted memorandum, underlying charges and the disposition of the inquiry. Senator's expressed suspicion of intervention is an allegation, not an independent finding on termination motive."
  true false false

record ChainReactionPromotionBoundary : Set where
  constructor chain-reaction-promotion-boundary
  field
    namedOriginalMemoIndexed : Bool
    memoLeadOnlyCaveatRetained : Bool
    senateInquiryActuallyPublished : Bool
    nativeMemoScanPageAuthenticated : Bool
    unredactedTargetsDisclosedHere : Bool
    namedBankWireMatchedToExistingLedger : Bool
    completedOperationDispositionVerified : Bool
    independentlyAdjudicatedDrugOffence : Bool
    investigationTerminationMotiveProven : Bool
    epsteinBlackNdaSameTransactionPaid : Bool
    aquinoSCLOrMaxwellPROMISSharedOperationPaid : Bool
open ChainReactionPromotionBoundary public

canonicalChainReactionPromotionBoundary : ChainReactionPromotionBoundary
canonicalChainReactionPromotionBoundary = chain-reaction-promotion-boundary
  true true true false false false false false false false false

chainReactionNamedSourcePaid :
  namedOriginalMemoIndexed canonicalChainReactionPromotionBoundary ≡ true
chainReactionNamedSourcePaid = refl

chainReactionLeadNotAdjudication :
  independentlyAdjudicatedDrugOffence canonicalChainReactionPromotionBoundary ≡ false
chainReactionLeadNotAdjudication = refl

chainReactionTerminationNotEstablished :
  investigationTerminationMotiveProven canonicalChainReactionPromotionBoundary ≡ false
chainReactionTerminationNotEstablished = refl

chainReactionNoAutoBlackLedgerJoin :
  epsteinBlackNdaSameTransactionPaid canonicalChainReactionPromotionBoundary ≡ false
chainReactionNoAutoBlackLedgerJoin = refl

chainReactionNoGlobalProgrammeTransfer :
  aquinoSCLOrMaxwellPROMISSharedOperationPaid canonicalChainReactionPromotionBoundary ≡ false
chainReactionNoGlobalProgrammeTransfer = refl


------------------------------------------------------------------------
-- MARCH 18 2026 WYDEN/BLANCHE ORIGINAL LETTER: FOLLOW-UP IS ONE SENATE
-- INQUIRY ROOT, NOT INDEPENDENT EVIDENCE OF INTERFERENCE OR PROSECUTION.
------------------------------------------------------------------------

chainReactionWydenMarch18 : ChainReactionSourceReceipt
chainReactionWydenMarch18 = chain-reaction-source-receipt
  laterSenateInquiryInterpretation
  "https://www.finance.senate.gov/ranking-members-news/wyden-sounds-alarm-as-dag-blanche-intervenes-to-conceal-details-of-mystery-epstein-investigation"
  "2026-03-18" "2026-03-18"
  "Wyden says his office received a confidential tip that DEA was ready to disclose a fuller OCDETF memo and that Deputy AG Blanche intervened. This proves the senator made the assertion and correspondence was sent, NOT that intervention or unlawful withholding was independently authenticated."
  true false false

record ChainReactionOversightAttributionCut : Set where
  constructor chain-reaction-oversight-attribution-cut
  field
    february2026SenateInquiryPublished : Bool
    march2026FollowupOriginalLetterPublished : Bool
    marchClaimReliedOnConfidentialTip : Bool
    februaryAndMarchAreSeparateInvestigatorRoots : Bool
    independentDEAInternalInterventionInstructionInspected : Bool
    actualCourtFindingOfObstruction : Bool
    originalOperationFinalDispositionVerified : Bool
    originalRedactedMemoIsFinishedCriminalFinding : Bool
open ChainReactionOversightAttributionCut public

canonicalChainReactionOversightAttributionCut : ChainReactionOversightAttributionCut
canonicalChainReactionOversightAttributionCut =
  chain-reaction-oversight-attribution-cut true true true false false false false false

marchAllegationIsNotAuthenticatedIntervention :
  independentDEAInternalInterventionInstructionInspected
    canonicalChainReactionOversightAttributionCut ≡ false
marchAllegationIsNotAuthenticatedIntervention = refl

wydenFollowupsDoNotCreateIndependentSecondSource :
  februaryAndMarchAreSeparateInvestigatorRoots
    canonicalChainReactionOversightAttributionCut ≡ false
wydenFollowupsDoNotCreateIndependentSecondSource = refl

ocdetfOutcomeNotProvenBySenateComplaint :
  originalOperationFinalDispositionVerified
    canonicalChainReactionOversightAttributionCut ≡ false
ocdetfOutcomeNotProvenBySenateComplaint = refl


------------------------------------------------------------------------
-- 2026-10-25 PARETO/Ibrahim ORIGINAL-NAME HOMONYM DISCRIMINATOR
--
-- The original HSI/IPR Center Operation Chain Reaction is a 2011-onward
-- counterfeit DOD/government microelectronics supply-chain initiative.
-- It is NOT the DEA/OCDETF 2010-opened NY-NYS-0829 investigation with
-- 2015 Epstein Target 4 memo EFTA00173953. Shared title, Federal
-- participation, and generic interagency language cannot join cases.
--
-- The original 2019 HSI factsheet was parsed AND visually inspected;
-- the 2022 House hearing is an official attributed HSI description.
-- Neither is the DEA operational disposition or an Epstein payment.
------------------------------------------------------------------------

record ChainReactionFederalNameCollisionCut : Set where
  constructor chain-reaction-federal-name-collision-cut
  field
    hsiIPR2019FactSheetOriginalInspected : Bool
    hsiIPR2019FactSheetSaysStartedJune2011 : Bool
    hsiTargetIsCounterfeitGovernmentSupplyChain : Bool
    hsiMicroelectronicsFocus : Bool
    hsiListedSixteenFederalAndOtherAgencyPartners : Bool
    house2022IndependentPublicHearingCarrier : Bool
    house2022IsSecondIndependentHSIInvestigator : Bool
    dea2015MemoCaseNYNYS0829Located : Bool
    deaOperationStart2010IndexedIn2015Memo : Bool
    sameNameMeansSameInvestigation : Bool
    agencyOverlapMeansSharedCaseIdentity : Bool
    hsiCounterfeitCasesAreDEADrugOffenceDispositions : Bool
    reportedJune2023DEAClosureHasSignedNativeInstrumentHere : Bool
    sourceProvesEitherCoverupOrSameEpsteinBankTransfer : Bool
open ChainReactionFederalNameCollisionCut public

canonicalChainReactionFederalNameCollisionCut : ChainReactionFederalNameCollisionCut
canonicalChainReactionFederalNameCollisionCut =
  chain-reaction-federal-name-collision-cut
  true true true true true true false true true false false false false false

hsiOperationOriginalFactSheetLocated :
  hsiIPR2019FactSheetOriginalInspected canonicalChainReactionFederalNameCollisionCut ≡ true
hsiOperationOriginalFactSheetLocated = refl

hsi2022HearingNotSecondIndependentInvestigation :
  house2022IsSecondIndependentHSIInvestigator canonicalChainReactionFederalNameCollisionCut ≡ false
hsi2022HearingNotSecondIndependentInvestigation = refl

sameOperationNameDoesNotPayCaseIdentity :
  sameNameMeansSameInvestigation canonicalChainReactionFederalNameCollisionCut ≡ false
sameOperationNameDoesNotPayCaseIdentity = refl

participatingFederalAgenciesDoNotPayCommonTasking :
  agencyOverlapMeansSharedCaseIdentity canonicalChainReactionFederalNameCollisionCut ≡ false
participatingFederalAgenciesDoNotPayCommonTasking = refl

hsiCounterfeitCasesDoNotDisposeDEAInquiry :
  hsiCounterfeitCasesAreDEADrugOffenceDispositions canonicalChainReactionFederalNameCollisionCut ≡ false
hsiCounterfeitCasesDoNotDisposeDEAInquiry = refl

secondaryClosureDateNotNativeSignedDEADisposition :
  reportedJune2023DEAClosureHasSignedNativeInstrumentHere
    canonicalChainReactionFederalNameCollisionCut ≡ false
secondaryClosureDateNotNativeSignedDEADisposition = refl

sameNameCollisionDoesNotPayBankWireOrCoverup :
  sourceProvesEitherCoverupOrSameEpsteinBankTransfer
    canonicalChainReactionFederalNameCollisionCut ≡ false
sameNameCollisionDoesNotPayBankWireOrCoverup = refl

hsiChainReaction2019NativeLocator : String
hsiChainReaction2019NativeLocator =
  "https://www.iprcenter.gov/file-repository/ipu-operation-chain-reaction.pdf ; original HSI/IPR Center factsheet updated January 2019, page 1; operation began June 2011."

hsiChainReactionCongressionalCarrier : String
hsiChainReactionCongressionalCarrier =
  "https://www.govinfo.gov/content/pkg/CHRG-117hhrg50981/html/CHRG-117hhrg50981.htm ; November 15 2022 House Homeland Security hearing describing HSI counterfeit goods, not DEA C1-11-0049."

deaChainReactionDistinctCaseLocator : String
deaChainReactionDistinctCaseLocator =
  "EFTA00173953 ; 2015-05-18 ; DEA / OCDETF NY-NYS-0829 / C1-11-0049; original native scan not independently page authenticated in this case."

chainReaction2023ReportedClosingDateOnly : String
chainReaction2023ReportedClosingDateOnly =
  "2023-06-16, as attributed to Bloomberg March 2026 by subsequent secondary sources; original signed DEA closing instrument uninspected. The date may be a discovery lead, not closed outcome evidence."


hsiChainReaction2011ContemporaneousSenateCarrier : String
hsiChainReaction2011ContemporaneousSenateCarrier =
  "2011-06-22 Senate Judiciary original hearing S.HRG.112-922, testimony by ICE Assistant Deputy Director Erik Barnett: ICE-led operation Chain Reaction was announced the prior week against counterfeit sales to federal government / military, govinfo CHRG-112shrg92565 hearing PDF page index 17. Original government published hearing text located; screenshot of page 17 timed out, so native page-image receipt is not certified. This is early HSI programme testimony, NOT 2010-opened DEA operation NY-NYS-0829."

hsiChainReaction2011FirstPersonAttribution : String
hsiChainReaction2011FirstPersonAttribution =
  "Erik Barnett, ICE Assistant Deputy Director, testifying 2011-06-22; contemporaneous witness speaking for HSI/ICE programme, distinct dated witness product from later HSI 2019 factsheet but overlapping same institution; count as a chronology corroboration, NOT independent DEA oversight or DEA closure receipt."


------------------------------------------------------------------------
-- 2026-10-26 EXACT CONSUMER NO-GO: A FEDERAL OPERATION'S PUBLIC TITLE
-- CANNOT SERVE AS ITS UNIQUE CASE IDENTIFIER.
--
-- Reuse existing IntersectionalNonFactorability witness/theorem on this
-- branch, NOT sibling #1266's unmerged ConsumerFactorization owner.
-- The two source-attributed agencies and subjects are factual input from
-- the original HSI/DEA records above. The following *finite mathematics*
-- proves an implication of this deliberately scoped representation only.
-- Original nonfactorability owner retains its cited historical provenance.
-- User-directed specific model: Johl Brown; AI-assisted formal adapter.
------------------------------------------------------------------------

data ChainReactionCaseIdentity : Set where
  deaOCDETFNYNYS0829 : ChainReactionCaseIdentity
  hsiIPRCounterfeit2011 : ChainReactionCaseIdentity

data ChainReactionTitleOnly : Set where
  operationChainReactionTitle : ChainReactionTitleOnly

casePublicHeadline : ChainReactionCaseIdentity → ChainReactionTitleOnly
casePublicHeadline _ = operationChainReactionTitle

caseIsDEA : ChainReactionCaseIdentity → Bool
caseIsDEA deaOCDETFNYNYS0829 = true
caseIsDEA hsiIPRCounterfeit2011 = false

noEqualityBetweenDEAAndHSITarget : true ≡ false → ⊥
noEqualityBetweenDEAAndHSITarget ()

originalFederalNameCollisionWitness :
  NonFactor.NonFactorabilityWitness casePublicHeadline caseIsDEA
originalFederalNameCollisionWitness =
  NonFactor.nonFactorabilityWitness
    deaOCDETFNYNYS0829 hsiIPRCounterfeit2011 refl
    noEqualityBetweenDEAAndHSITarget

nameOnlyFederalCaseIdentityImpossible :
  NonFactor.FactorsThrough casePublicHeadline caseIsDEA → ⊥
nameOnlyFederalCaseIdentityImpossible =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    originalFederalNameCollisionWitness

-- Any downstream sorting/reformatting of the *name alone* inherits
-- the collision; no amount of extra articles quoting that same title
-- can recover an agency/case-specific identity from the title projection.
nameReformattingDoesNotResolveFederalCases :
  ∀ {NewLabel : Set} →
  (reformat : ChainReactionTitleOnly → NewLabel) →
  NonFactor.FactorsThrough
    (λ caseId → reformat (casePublicHeadline caseId)) caseIsDEA → ⊥
nameReformattingDoesNotResolveFederalCases reformat =
  NonFactor.rechartingCannotRecoverErasedPhenomenon
    reformat originalFederalNameCollisionWitness

-- A richer original agency+case-ID carrier is sufficient *in this
-- two-case fixture*, but its labels must still be authenticated as
-- originals in the empirical source-acquisition stage.
data OriginalFederalCaseKey : Set where
  deaCaseNYNYS0829 : OriginalFederalCaseKey
  hsiCounterfeitSupplyChain : OriginalFederalCaseKey

originalFederalCaseKey : ChainReactionCaseIdentity → OriginalFederalCaseKey
originalFederalCaseKey deaOCDETFNYNYS0829 = deaCaseNYNYS0829
originalFederalCaseKey hsiIPRCounterfeit2011 = hsiCounterfeitSupplyChain

keyIdentifiesDEA : OriginalFederalCaseKey → Bool
keyIdentifiesDEA deaCaseNYNYS0829 = true
keyIdentifiesDEA hsiCounterfeitSupplyChain = false

originalCaseKeyConsumerFactors :
  NonFactor.FactorsThrough originalFederalCaseKey caseIsDEA
originalCaseKeyConsumerFactors =
  NonFactor.factorsThrough keyIdentifiesDEA (λ caseId → caseIdEq caseId)
  where
    caseIdEq : (caseId : ChainReactionCaseIdentity) →
      caseIsDEA caseId ≡ keyIdentifiesDEA (originalFederalCaseKey caseId)
    caseIdEq deaOCDETFNYNYS0829 = refl
    caseIdEq hsiIPRCounterfeit2011 = refl
