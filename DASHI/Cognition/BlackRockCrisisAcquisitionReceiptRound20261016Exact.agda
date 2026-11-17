module DASHI.Cognition.BlackRockCrisisAcquisitionReceiptRound20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.SystemicLeverageBeneficiaryIncidenceParetoExact as Incidence

------------------------------------------------------------------------
-- BLACKROCK / CRISIS-STATE ACQUISITION RECEIPT ROUND — 2026-10-16
--
-- Pays several previously open public-document leaves from the ordered crisis
-- incidence frontier. The central result is not that BlackRock/Fink authored
-- the bailouts. It is that advisory/implementation access, reciprocal capital
-- topology, public-contract revenue and delayed distributional incidence can be
-- resolved separately on the same crisis timeline.
------------------------------------------------------------------------

data ReceiptSurface : Set where
  finkTARPAdviceImplementedPolicyDivergence : ReceiptSurface
  merrillBlackRockCapitalOwnership2008 : ReceiptSurface
  bankOfAmericaMerrillBlackRockContinuity2009 : ReceiptSurface
  cppVersusHousingTimingScale2010 : ReceiptSurface
  cppPublicRecovery2019 : ReceiptSurface
  fed2020BlackRockFeeAndConflictCredit : ReceiptSurface
  fed2020AuthorityAndUtilization : ReceiptSurface

record CrisisAcquisitionReceipt : Set where
  constructor crisis-acquisition-receipt
  field
    surface : ReceiptSurface
    source : String
    boundedFinding : String
    order : Incidence.EffectOrder
    sourcePaid : Bool
    cashOrOwnershipCoordinatePaid : Bool
    causalAuthorshipPaid : Bool
open CrisisAcquisitionReceipt public

finkAdviceDivergence : CrisisAcquisitionReceipt
finkAdviceDivergence = crisis-acquisition-receipt
  finkTARPAdviceImplementedPolicyDivergence
  "GovInfo CHRG-111hhrg49968, reproduced crisis-profile testimony/reporting; Treasury CPP records"
  "Fink said he counselled Treasury Secretary Henry Paulson to use TARP funds to purchase troubled/toxic assets. Paulson instead implemented preferred-equity capital injections into banks. This pays material advisory access and a documented recommendation, while the divergence between recommendation and implemented policy directly blocks the stronger proposition that Fink authored the bank-equity recipient programme."
  Incidence.firstOrder true false false

merrillOwnsBlackRock2008 : CrisisAcquisitionReceipt
merrillOwnsBlackRock2008 = crisis-acquisition-receipt
  merrillBlackRockCapitalOwnership2008
  "BlackRock 2008/2009 SEC filings"
  "At 31 December 2008 Merrill Lynch owned approximately 44.2% of BlackRock voting common stock and approximately 48.2% of BlackRock capital stock on a fully diluted basis. Merrill Lynch was one of the initial CPP institutions. This pays a large reverse ownership edge: a crisis-supported financial institution was itself a major BlackRock owner."
  Incidence.secondOrder true true false

boaMerrillContinuity : CrisisAcquisitionReceipt
boaMerrillContinuity = crisis-acquisition-receipt
  bankOfAmericaMerrillBlackRockContinuity2009
  "BlackRock 2009 10-K / SEC filings"
  "Bank of America acquired Merrill Lynch on 1 January 2009. After the February 2009 BlackRock share exchanges, Bank of America/Merrill retained about 47.4% of BlackRock capital on a fully diluted basis; at year-end 2009 the reported capital-stock position was about 34.2%. This is concrete post-crisis reciprocal capital topology, not evidence that BlackRock selected Bank of America or Merrill for CPP support."
  Incidence.secondOrder true true false

cppHousingTiming2010 : CrisisAcquisitionReceipt
cppHousingTiming2010 = crisis-acquisition-receipt
  cppVersusHousingTimingScale2010
  "GAO-11-74 / GAO TARP programme status records"
  "By 30 September 2010 CPP had disbursed about USD204.9bn to financial institutions, while TARP-funded housing programmes had disbursed about USD543m. HAMP had been announced in March 2009 and implemented in April 2009. This pays a large timing-and-scale asymmetry in direct programme disbursement without asserting that bank support and homeowner assistance are economically identical instruments."
  Incidence.secondOrder true true false

cppPublicRecovery : CrisisAcquisitionReceipt
cppPublicRecovery = crisis-acquisition-receipt
  cppPublicRecovery2019
  "GAO-20-218R"
  "Treasury's CPP investment was about USD204.90bn; by 30 September 2019 Treasury had received about USD226.77bn in repayments and income from CPP investments and sales. This pays substantial public financial recovery on the direct capital programme and prevents a one-way-gift representation, while it does not erase distributional or opportunity costs."
  Incidence.secondOrder true true false

fed2020FeeConflict : CrisisAcquisitionReceipt
fed2020FeeConflict = crisis-acquisition-receipt
  fed2020BlackRockFeeAndConflictCredit
  "Federal Reserve Bank of New York 13(3) facility vendor-cost reports and SMCCF investment-management amendment"
  "Official life-to-date vendor reporting records USD8,172,327 of BlackRock SMCCF investment-management/advisory cost and a USD6,544,399 BlackRock ETF-revenue credit. The contract was amended so BlackRock revenues from affiliated ETFs held by the facility were credited back to the facility. This pays direct fee revenue and an explicit same-firm conflict-mitigation mechanism rather than either ignoring the conflict surface or treating it as proof of self-dealing."
  Incidence.firstOrder true true false

fed2020AuthorityUtilization : CrisisAcquisitionReceipt
fed2020AuthorityUtilization = crisis-acquisition-receipt
  fed2020AuthorityAndUtilization
  "Federal Reserve / New York Fed CCF FAQs; GAO-21-180"
  "BlackRock served as investment manager at the sole direction of the New York Fed and was required to follow Federal Reserve investment guidelines. GAO reported about USD13.6bn of PMCCF/SMCCF transaction volume against a combined stated maximum size of USD750bn. Maximum facility capacity, actual asset purchases and broader monetary expansion are therefore distinct observables."
  Incidence.firstOrder true true false

allAcquisitionReceipts : List CrisisAcquisitionReceipt
allAcquisitionReceipts =
  finkAdviceDivergence
  ∷ merrillOwnsBlackRock2008
  ∷ boaMerrillContinuity
  ∷ cppHousingTiming2010
  ∷ cppPublicRecovery
  ∷ fed2020FeeConflict
  ∷ fed2020AuthorityUtilization
  ∷ []

------------------------------------------------------------------------
-- Strong non-collapse consequences of the newly paid receipts.
------------------------------------------------------------------------

data AdviserRecommendationImpliesImplementedPolicy : Set where
data ReverseOwnershipImpliesRecipientSelection : Set where
data CrisisSupportedOwnerImpliesBlackRockBailout : Set where
data ContractFeeImpliesMonetaryPolicyAuthority : Set where
data ETFConflictSurfaceImpliesSelfDealing : Set where
data PublicFinancialRecoveryErasesDistributionalCost : Set where
data MaximumFacilitySizeEqualsActualPurchases : Set where

divergentAdviceDoesNotCreateImplementedPolicy : AdviserRecommendationImpliesImplementedPolicy → ⊥
divergentAdviceDoesNotCreateImplementedPolicy ()

reverseOwnershipDoesNotCreateRecipientSelection : ReverseOwnershipImpliesRecipientSelection → ⊥
reverseOwnershipDoesNotCreateRecipientSelection ()

supportedOwnerDoesNotCreateBlackRockBailout : CrisisSupportedOwnerImpliesBlackRockBailout → ⊥
supportedOwnerDoesNotCreateBlackRockBailout ()

contractFeeDoesNotCreateMonetaryAuthority : ContractFeeImpliesMonetaryPolicyAuthority → ⊥
contractFeeDoesNotCreateMonetaryAuthority ()

conflictSurfaceDoesNotCreateSelfDealing : ETFConflictSurfaceImpliesSelfDealing → ⊥
conflictSurfaceDoesNotCreateSelfDealing ()

publicRecoveryDoesNotEraseDistributionalCost : PublicFinancialRecoveryErasesDistributionalCost → ⊥
publicRecoveryDoesNotEraseDistributionalCost ()

maximumSizeDoesNotEqualPurchases : MaximumFacilitySizeEqualsActualPurchases → ⊥
maximumSizeDoesNotEqualPurchases ()

------------------------------------------------------------------------
-- Refined benefit-order interpretation.
------------------------------------------------------------------------

reverseOwnershipSecondOrder : Incidence.SystemicLeverageCandidate
reverseOwnershipSecondOrder = Incidence.systemic-leverage-candidate
  "CPP recipient -> BlackRock ownership topology"
  Incidence.secondOrder
  Incidence.marketStructure
  "How did crisis-supported institutions' large ownership positions in BlackRock alter reciprocal exposure, governance rights, option value and later divestment choices?"
  "Merrill/Bank of America held a large economic BlackRock position, while BlackRock gained from a continuing distribution/shareholder relationship; exact mark-to-market incidence requires dated valuation."
  "Taxpayers and non-supported competitors can bear opportunity/risk burdens; BlackRock minority shareholders face concentration/governance effects."
  "Separate voting power, economic ownership, board rights, distribution agreements and sovereign rescue authority."
  "BlackRock SEC ownership tables, stockholder agreements, CPP transaction dates, dated BlackRock prices and later sale records"
  true false false

homeownerTemporalSecondOrder : Incidence.SystemicLeverageCandidate
homeownerTemporalSecondOrder = Incidence.systemic-leverage-candidate
  "institution support -> delayed homeowner relief"
  Incidence.secondOrder
  Incidence.externalityShift
  "How much earlier and larger was direct institution capital support than household foreclosure relief, and which losses were shifted or avoided in each channel?"
  "Banks, creditors and counterparties obtained immediate stabilisation; eligible homeowners obtained later modification/foreclosure relief."
  "Ineligible or foreclosed households, renters and workers can bear crisis/deleveraging burdens before assistance arrives."
  "Who set programme eligibility, servicing discretion, modification terms and timing, and who could contest denial?"
  "monthly CPP/HAMP/HHF cash flows, eligibility, foreclosure and modification cohorts, servicer records"
  true false false

publicPrivateFeedbackThirdOrder : Incidence.SystemicLeverageCandidate
publicPrivateFeedbackThirdOrder = Incidence.systemic-leverage-candidate
  "crisis advisory -> reusable private crisis infrastructure"
  Incidence.thirdOrder
  Incidence.institutionalControl
  "Does repeated public use of private financial managers convert crisis work into durable reputational, data/model, relationship or selection advantages?"
  "Incumbent managers can gain future-selection option value; public institutions gain immediately deployable specialist capacity."
  "Competing providers and public internal capability can lose relative position if expertise and operational data concentrate outside government."
  "Who owns models/data, controls procurement, defines eligibility, can replace the vendor and retains institutional memory?"
  "2008 and 2020 contracts, procurement rationales, model/data ownership clauses, staff continuity, competitor bids and internal-capability records"
  false false false

------------------------------------------------------------------------
-- Remaining acquisition after this round.
------------------------------------------------------------------------

data RoundDebt : Set where
  nineCPPBlackRockManagedHoldings : RoundDebt
  finkPersonalHoldingsSnapshot : RoundDebt
  merrillBlackRockMarkToMarketIncidence : RoundDebt
  maidenLaneExactFeesAndClientExposure : RoundDebt
  ccfCUSIPBeneficialOwnerIncidence : RoundDebt
  mandateReselectionMechanism : RoundDebt
  householdInstitutionOutcomeCounterfactual : RoundDebt

record RoundAcquisition : Set where
  constructor round-acquisition
  field
    debt : RoundDebt
    priority : Nat
    order : Incidence.EffectOrder
    instruction : String
open RoundAcquisition public

canonicalRoundAcquisition : List RoundAcquisition
canonicalRoundAcquisition =
  round-acquisition nineCPPBlackRockManagedHoldings 100 Incidence.secondOrder
    "Resolve actual BlackRock-managed common/debt exposure across each of the initial nine CPP institutions at pre-announcement and post-announcement dates. The 'eight of nine' viral claim remains unpaid until this table exists." ∷
  round-acquisition finkPersonalHoldingsSnapshot 100 Incidence.secondOrder
    "Resolve Larry Fink's personal beneficial positions separately from BlackRock-managed client/fund holdings; AUM and manager voting authority are not personal ownership." ∷
  round-acquisition merrillBlackRockMarkToMarketIncidence 100 Incidence.secondOrder
    "Join Merrill/Bank of America's paid 48.2%/47.4% BlackRock capital position to dated BlackRock equity values and later sales to quantify the actual reciprocal crisis-era ownership benefit/loss rather than merely noting topology." ∷
  round-acquisition ccfCUSIPBeneficialOwnerIncidence 99 Incidence.secondOrder
    "Map published 2020 CCF purchases by CUSIP/ETF to sellers, contemporaneous holders and issuer financing conditions; separate direct sale proceeds, spread compression, mark-to-market gains and manager fee/AUM effects." ∷
  round-acquisition maidenLaneExactFeesAndClientExposure 99 Incidence.firstOrder
    "Acquire exact Maiden Lane I/II/III BlackRock fee schedules and contemporaneous BlackRock-client positions in the same securities to quantify direct contractual gain and conflict exposure." ∷
  round-acquisition mandateReselectionMechanism 99 Incidence.thirdOrder
    "Resolve personnel/model/data continuity from 2008 to 2020 and compare procurement alternatives to test whether prior crisis work causally increased later selection probability." ∷
  round-acquisition householdInstitutionOutcomeCounterfactual 98 Incidence.thirdOrder
    "Move beyond cash-flow asymmetry to causal outcome comparison: foreclosure avoidance, unemployment/credit effects, bank solvency and public recovery under credible counterfactual intervention designs."
  ∷ []
