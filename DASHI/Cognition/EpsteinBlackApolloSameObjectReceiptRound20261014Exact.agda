module DASHI.Cognition.EpsteinBlackApolloSameObjectReceiptRound20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinBankingInfrastructureAcquisitionExact as Banking
import DASHI.Cognition.EpsteinFinanceTechParetoRoundExact as Finance

------------------------------------------------------------------------
-- EPSTEIN / LEON BLACK / APOLLO SAME-OBJECT RECEIPT ROUND — 2026-10-14
--
-- The central correction is that "Apollo never retained Epstein" and
-- "Epstein had no Apollo-related financial edge" are not equivalent claims.
-- The public record supports several narrow Apollo-related coordinates while
-- still supporting the absence of an Epstein investment in Apollo-managed
-- funds and the absence of an Apollo corporate retainer for Epstein.
------------------------------------------------------------------------

data BlackApolloSurface : Set where
  personalAdvisory : BlackApolloSurface
  blackFamilyOffice : BlackApolloSurface
  apolloOwnershipInterestTaxPlanning : BlackApolloSurface
  apolloPublicEquity : BlackApolloSurface
  apolloExecutiveSideVehicle : BlackApolloSurface
  coInvestmentWithBlackFamily : BlackApolloSurface
  professionalServicePayment : BlackApolloSurface
  loan : BlackApolloSurface
  philanthropy : BlackApolloSurface
  bankProcessing : BlackApolloSurface
  congressionalFinding : BlackApolloSurface

record SameObjectReceipt : Set where
  constructor same-object-receipt
  field
    label : String
    surface : BlackApolloSurface
    source : String
    boundedFinding : String
    primaryOrOfficial : Bool
    relationPaid : Bool
    apolloCorporateRetainerPaid : Bool
    apolloManagedFundInvestmentPaid : Bool
    wrongdoingPaidByThisReceipt : Bool
open SameObjectReceipt public

blackEpsteinAdvisory158m : SameObjectReceipt
blackEpsteinAdvisory158m = same-object-receipt
  "Dechert Black-Epstein advisory total"
  professionalServicePayment
  "SEC-filed Dechert report, 2021-01-22"
  "The Apollo Conflicts Committee review found Black paid Epstein USD 158 million from 2013 through 2017 for tax, estate-planning and related Family Office advice. The report attributes USD 50m to 2013, USD 70m to 2014, USD 30m to 2015, no payment in 2016 and USD 8m in April 2017."
  true true false false false

senateBlackEpstein170m : SameObjectReceipt
senateBlackEpstein170m = same-object-receipt
  "Senate/Treasury Black-Epstein payment total"
  congressionalFinding
  "Senate Finance letter to DOJ/Treasury/FBI, 2025-03-11; 2026 follow-up"
  "Senate Finance states federal records identified additional wire transfers omitted from the Dechert total and place Black-controlled-account payments to Epstein entities at more than USD 170 million. This is an attributed congressional finding based on Treasury records and does not silently rewrite the narrower Dechert service-fee ledger."
  true true false false false

blackAccountsToEpsteinEntities : SameObjectReceipt
blackAccountsToEpsteinEntities = same-object-receipt
  "Black-controlled accounts to Southern/Financial Trust"
  bankProcessing
  "Senate Finance Treasury-record review, 2025-03-11"
  "Senate Finance states Black-controlled accounts including Leon Black, Debra Black, Black Family Partners LP, Narrows Holdings LLC, Elysium Management LLC and Melanie Spinella sent roughly USD 170m to Epstein-controlled Southern Trust Company and Financial Trust Company; about USD 140m was transferred to Southern Trust accounts at Deutsche Bank during 2013-2015."
  true true false false false

blackSouthernTrust2013Contract : SameObjectReceipt
blackSouthernTrust2013Contract = same-object-receipt
  "Black-Southern Trust written services agreement"
  personalAdvisory
  "SEC-filed Dechert report, 2021-01-22"
  "A February 2013 agreement between Black and Epstein affiliate Southern Trust Company covered estate-planning services; Dechert records USD 15m and USD 8.5m installment payments in 2013."
  true true false false false

blackEpsteinLoans2017 : SameObjectReceipt
blackEpsteinLoans2017 = same-object-receipt
  "BV70-to-Plan D loans"
  loan
  "SEC-filed Dechert report, 2021-01-22"
  "Black-owned BV70 LLC made two documented early-2017 loans of USD 22.5m and USD 8m to Epstein-owned Plan D LLC in connection with an art transaction; Epstein repaid USD 10m and the remainder was unpaid at his death according to Dechert. These loans are separate from service fees."
  true true false false false

blackGratitudeAmericaDonation : SameObjectReceipt
blackGratitudeAmericaDonation = same-object-receipt
  "Black donation to Epstein-affiliated Gratitude America"
  philanthropy
  "SEC-filed Dechert report, 2021-01-22"
  "Dechert found Black made a USD 10m donation to Epstein-affiliated Gratitude America in October 2015 and records additional philanthropy at Epstein's request; a separate alleged USD 5m Gratitude America donation had a thank-you letter/email but no Black-side bank record located by Dechert."
  true true false false false

epsteinApolloIPOStock : SameObjectReceipt
epsteinApolloIPOStock = same-object-receipt
  "Epstein entity Apollo IPO stock purchase"
  apolloPublicEquity
  "SEC-filed Dechert report, 2021-01-22"
  "Dechert found Epstein-owned Financial Trust Company purchased 263,257 Apollo shares in Apollo's 2011 IPO through the directed-share program; the shares appear to have transferred in 2013 to Epstein-affiliated Southern Financial LLC and remained there through at least September 2019. This is Apollo public-equity exposure, not an Apollo-managed-fund investment or corporate retainer."
  true true false false false

epsteinApolloExecutiveSideVehicles : SameObjectReceipt
epsteinApolloExecutiveSideVehicles = same-object-receipt
  "Epstein passive investment alongside Apollo executives"
  apolloExecutiveSideVehicle
  "SEC-filed Dechert report, 2021-01-22"
  "Dechert found Financial Trust Company invested in AP SHL Investors LLC and AP Technology Partners LLC, vehicles formed by certain Apollo executives to explore opportunities Apollo chose not to pursue. The report says these were not Apollo entities and found Epstein to be a passive investor."
  true true false false false

epsteinESWWCoInvestment : SameObjectReceipt
epsteinESWWCoInvestment = same-object-receipt
  "Epstein/Black-family ESWW co-investment"
  coInvestmentWithBlackFamily
  "SEC-filed Dechert report, 2021-01-22"
  "Dechert found Financial Trust Company appears to have invested in Environmental Solutions World Wide in 2011 alongside Black and certain Black family members. This pays a co-investment edge and nothing more."
  true true false false false

epsteinApolloOwnershipTaxAdvice : SameObjectReceipt
epsteinApolloOwnershipTaxAdvice = same-object-receipt
  "Epstein advice on Black Apollo ownership-interest tax filings"
  apolloOwnershipInterestTaxPlanning
  "SEC-filed Dechert report; Senate Finance 2023 trust inquiry"
  "Dechert states Epstein helped manage tax-compliance issues relating to BRH Holdings LP, the partnership through which Black and other Apollo co-founders held Apollo ownership interests. Senate Finance separately states Black's 2006 GRATs were funded by large percentage interests in multiple Apollo management/advisory partnerships. This pays an Apollo-ownership-interest tax-planning coordinate through Black's personal/family structures, not an Apollo corporate retainer."
  true true false false false

apolloNoCorporateRetainer : SameObjectReceipt
apolloNoCorporateRetainer = same-object-receipt
  "No Apollo corporate retainer identified"
  personalAdvisory
  "SEC-filed Dechert report; Apollo 2026 client letter"
  "Dechert reported no indication Apollo ever retained Epstein and no Epstein investment in Apollo-managed funds; Apollo repeated in 2026 that Black was the only Apollo principal with the paid personal advisory relationship, while noting that select Apollo employees supplied information connected to Black's tax work. This bounded negative does not erase the IPO-stock, side-vehicle, ownership-interest-tax or introduction edges."
  true true false false false

record ApolloNuanceBoundary : Set where
  constructor apollo-nuance-boundary
  field
    epsteinHeldApolloPublicEquity : Bool
    epsteinInvestedInApolloManagedFund : Bool
    apolloCorporationRetainedEpstein : Bool
    epsteinAdvisedOnBlackApolloOwnershipInterests : Bool
    epsteinInvestedAlongsideSomeApolloExecutives : Bool
    blackTriedToIntroduceEpsteinToCoFounders : Bool
    theseEdgesEqualApolloCorporateEngagement : Bool
    apolloNegativeStatementErasesNarrowEdges : Bool
open ApolloNuanceBoundary public

canonicalApolloNuanceBoundary : ApolloNuanceBoundary
canonicalApolloNuanceBoundary = apollo-nuance-boundary
  true false false true true true false false

------------------------------------------------------------------------
-- Attribution firewalls.
------------------------------------------------------------------------

data PublicEquityImpliesCorporateRetainer : Set where
data SideVehicleImpliesApolloFund : Set where
data OwnershipTaxAdviceImpliesApolloClient : Set where
data IntroductionAttemptImpliesRetention : Set where
data CongressionalWireFindingImpliesCriminalConviction : Set where
data LargePaymentImpliesIllicitPurpose : Set where
data USVISettlementImpliesAdmissionOfAllAllegations : Set where

publicEquityDoesNotCreateRetainer : PublicEquityImpliesCorporateRetainer → ⊥
publicEquityDoesNotCreateRetainer ()

sideVehicleDoesNotCreateApolloFund : SideVehicleImpliesApolloFund → ⊥
sideVehicleDoesNotCreateApolloFund ()

ownershipTaxAdviceDoesNotCreateApolloClient : OwnershipTaxAdviceImpliesApolloClient → ⊥
ownershipTaxAdviceDoesNotCreateApolloClient ()

introductionAttemptDoesNotCreateRetention : IntroductionAttemptImpliesRetention → ⊥
introductionAttemptDoesNotCreateRetention ()

congressionalWireFindingDoesNotCreateConviction : CongressionalWireFindingImpliesCriminalConviction → ⊥
congressionalWireFindingDoesNotCreateConviction ()

largePaymentDoesNotCreateIllicitPurpose : LargePaymentImpliesIllicitPurpose → ⊥
largePaymentDoesNotCreateIllicitPurpose ()

usviSettlementDoesNotCreateUniversalAdmission : USVISettlementImpliesAdmissionOfAllAllegations → ⊥
usviSettlementDoesNotCreateUniversalAdmission ()

------------------------------------------------------------------------
-- Remaining acquisition is now transaction-object specific.
------------------------------------------------------------------------

data BlackApolloDebt : Set where
  exact170mWireLedger : BlackApolloDebt
  additional12mWirePurpose : BlackApolloDebt
  apolloIPOShareDispositionAfter2019 : BlackApolloDebt
  apSHLAndAPTechnologyUnderlyingDeals : BlackApolloDebt
  eswwPositionAndExit : BlackApolloDebt
  gratApolloInterestCurrentDisposition : BlackApolloDebt
  blackFamilyOfficeAdvisorCounterpartyGraph : BlackApolloDebt
  bankEmployeeDecisionChainForBlackWires : BlackApolloDebt
  black2026TranscriptReconciliation : BlackApolloDebt

record BlackApolloAcquisition : Set where
  constructor black-apollo-acquisition
  field
    debt : BlackApolloDebt
    priority : Nat
    sameObjectRequired : Bool
    question : String
open BlackApolloAcquisition public

canonicalBlackApolloAcquisition : List BlackApolloAcquisition
canonicalBlackApolloAcquisition =
  black-apollo-acquisition exact170mWireLedger 100 true
    "Recover the Treasury/SAR-level Black->Epstein wire ledger with date, payer account/entity, sending bank, recipient entity/bank, amount and stated/purported purpose; reconcile the Dechert USD 158m service ledger with Senate Finance's >USD 170m transaction total."
  ∷ black-apollo-acquisition additional12mWirePurpose 100 true
    "Resolve the additional wires totaling about USD 12m that Senate Finance says were absent from the Apollo/Dechert review, including purpose and whether they were fees, gifts, loans, reimbursements or another class."
  ∷ black-apollo-acquisition bankEmployeeDecisionChainForBlackWires 99 true
    "Identify the specific bank compliance/relationship-management chain that cleared, reviewed or delayed reporting Black-account wires to Epstein entities and distinguish institutional findings from individual knowledge."
  ∷ black-apollo-acquisition gratApolloInterestCurrentDisposition 99 true
    "Trace the Apollo management/advisory interests placed in Black's 2006 GRATs through valuations, distributions, retained voting/control rights and later disposition."
  ∷ black-apollo-acquisition blackFamilyOfficeAdvisorCounterpartyGraph 98 true
    "Map Paul Weiss, accounting/tax advisers, Elysium/Family Office personnel and other counterparties who originated, vetted, implemented or rejected each Epstein-proposed structure."
  ∷ black-apollo-acquisition apSHLAndAPTechnologyUnderlyingDeals 98 true
    "Resolve capitalization, managers, co-investors, investments and exits for AP SHL Investors and AP Technology Partners; keep them explicitly non-Apollo unless a formal Apollo relationship is independently paid."
  ∷ black-apollo-acquisition apolloIPOShareDispositionAfter2019 97 true
    "Trace the 263,257 Apollo IPO shares from Financial Trust Company to Southern Financial LLC and determine disposition/value after September 2019, including estate treatment."
  ∷ black-apollo-acquisition eswwPositionAndExit 96 true
    "Resolve Epstein's ESWW investment amount, Black/family co-investment structure, board/governance rights if any and exit chronology."
  ∷ black-apollo-acquisition black2026TranscriptReconciliation 95 true
    "Reconcile Black's June 2026 House Oversight testimony against Dechert, Senate Finance/Treasury and USVI settlement records claim by claim."
  ∷ []
