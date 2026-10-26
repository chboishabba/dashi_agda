module DASHI.Cognition.EpsteinPalantirInvestmentInterest20261015Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinThielValarDirectSolicitation20261014Exact as Valar
import DASHI.Cognition.PalantirTIAFinanceStateCapacityCrossPollination20261015Exact as PalantirTIA

------------------------------------------------------------------------
-- EPSTEIN / PALANTIR INVESTMENT-INTEREST RECEIPTS — 2026-10-15
--
-- Released records pay direct Palantir investment inquiry/advice, direct
-- secondary-market pricing discussion with Palantir's co-founder/chairman, a
-- later secondary-share opportunity routed through Fiszel/Kahn, and later
-- valuation/company research.  They do not yet pay an executed purchase,
-- custody position, beneficial ownership, sale, board/governance right or
-- Palantir corporate client relationship.
------------------------------------------------------------------------

data InvestmentStage : Set where
  directInquiry : InvestmentStage
  directAdvice : InvestmentStage
  secondaryPricingNegotiation : InvestmentStage
  secondaryShareOpportunity : InvestmentStage
  companyDiligence : InvestmentStage
  completedPurchase : InvestmentStage
  custodyPosition : InvestmentStage
  realisedSale : InvestmentStage

record PalantirInvestmentReceipt : Set where
  constructor palantir-investment-receipt
  field
    label : String
    date : String
    source : String
    stage : InvestmentStage
    boundedFinding : String
    directEpsteinSurfacePaid : Bool
    completedInvestmentPaid : Bool
    palantirCorporateRelationshipPaid : Bool
open PalantirInvestmentReceipt public

thielPalantirAdvice2014 : PalantirInvestmentReceipt
thielPalantirAdvice2014 = palantir-investment-receipt
  "Epstein asks Thiel for Palantir investment view"
  "2014-10-27"
  "EFTA00664427"
  directAdvice
  "Epstein asked Thiel for his view on Spotify and Palantir. Thiel replied that he was somewhat more bullish on Palantir, saw no need to rush and suggested discussing it later in person. This pays direct investment inquiry/advice, not a purchase or completed later meeting."
  true false false

thielPalantirPricing2016 : PalantirInvestmentReceipt
thielPalantirPricing2016 = palantir-investment-receipt
  "Epstein consults Thiel on Palantir secondary-share price"
  "2016-10-14 to 2016-10-15"
  "EFTA02447787 / EFTA02447940 / EFTA02448060"
  secondaryPricingNegotiation
  "Released-record indexing reproduces a direct exchange in which Epstein says he is being offered a chunk of Palantir at USD5.50 per share and asks Thiel's view. Thiel describes USD5.50 as somewhat below market / at the lower range of recent transactions; Epstein identifies the seller as a mutual fund that wants to get out; Thiel asks which fund and says Epstein may be able to get a still better price within the next twelve months. This pays direct Palantir-specific secondary-market pricing advice and seller-type context, not an executed purchase, inside-information legal conclusion or beneficial holding."
  true false false

palantirSecondaryOpportunity2016 : PalantirInvestmentReceipt
palantirSecondaryOpportunity2016 = palantir-investment-receipt
  "Palantir secondary-share opportunity routed to Epstein"
  "2016-12-16"
  "HOUSE_OVERSIGHT_033208 / EFTA02666567 lineage"
  secondaryShareOpportunity
  "David Fiszel told Richard Kahn he could buy more Palantir at USD5 per share, described as about a USD9.5bn valuation; Kahn forwarded the opportunity to Epstein and characterised the access as roughly a 50% discount to market if Epstein's view was remotely positive. This pays a routed investment opportunity and advice request, not execution."
  true false false

palantirResearch2018 : PalantirInvestmentReceipt
palantirResearch2018 = palantir-investment-receipt
  "Palantir valuation / IPO diligence in Epstein-HBRK workflow"
  "2018-10-18"
  "EFTA01019243 / EFTA01019247 / EFTA00807234"
  companyDiligence
  "Kahn and Epstein exchanged Palantir IPO/valuation material; the released corpus includes a detailed PitchBook Palantir profile generated for Kahn. A nearby Fiszel/Kahn exchange includes Kahn forwarding Epstein the phrase 'hope you kept some stock', but the pronoun/holding referent is not sufficient by itself to establish Epstein ownership. Presence of research and suggestive language pays continued monitoring, not a custody statement or beneficial holding."
  true false false

record PalantirInvestmentBoundary : Set where
  constructor palantir-investment-boundary
  field
    directPalantirInvestmentInquiryPaid : Bool
    thielPalantirAdvicePaid : Bool
    directSecondaryPricingDiscussionPaid : Bool
    sellerTypeMutualFundPaid : Bool
    secondaryShareOpportunityPaid : Bool
    laterCompanyDiligencePaid : Bool
    completedPurchasePaid : Bool
    custodyPositionPaid : Bool
    realisedSalePaid : Bool
    boardOrGovernanceRightPaid : Bool
    palantirCorporateClientRelationshipPaid : Bool
    valarInvestmentImpliesPalantirInvestment : Bool
    suggestiveStockPhraseImpliesEpsteinHolding : Bool
open PalantirInvestmentBoundary public

canonicalPalantirInvestmentBoundary : PalantirInvestmentBoundary
canonicalPalantirInvestmentBoundary = palantir-investment-boundary
  true true true true true true false false false false false false false

data InvestmentInquiryImpliesPurchase : Set where
data ShareOpportunityImpliesPurchase : Set where
data DiligenceImpliesCustodyPosition : Set where
data ValarLPImpliesPalantirHolding : Set where
data SuggestiveStockPhraseImpliesHolding : Set where

directInquiryDoesNotCreatePurchase : InvestmentInquiryImpliesPurchase → ⊥
directInquiryDoesNotCreatePurchase ()

shareOpportunityDoesNotCreatePurchase : ShareOpportunityImpliesPurchase → ⊥
shareOpportunityDoesNotCreatePurchase ()

diligenceDoesNotCreateCustody : DiligenceImpliesCustodyPosition → ⊥
diligenceDoesNotCreateCustody ()

valarLPDoesNotCreatePalantirHolding : ValarLPImpliesPalantirHolding → ⊥
valarLPDoesNotCreatePalantirHolding ()

suggestivePhraseDoesNotCreateHolding : SuggestiveStockPhraseImpliesHolding → ⊥
suggestivePhraseDoesNotCreateHolding ()

------------------------------------------------------------------------
-- Cross-pollination with the already-paid Thiel -> Valar investment path.
------------------------------------------------------------------------

record ThielInvestmentAdviceComparison : Set where
  constructor thiel-investment-advice-comparison
  field
    valarDirectSolicitationPaid : Bool
    southernTrustValarInvestmentCompleted : Bool
    palantirDirectAdvicePaid : Bool
    palantirDirectPricingAdvicePaid : Bool
    palantirSecondaryOpportunityPaid : Bool
    palantirInvestmentCompleted : Bool
    sameAdviserImpliesSameOutcome : Bool
open ThielInvestmentAdviceComparison public

canonicalThielInvestmentAdviceComparison : ThielInvestmentAdviceComparison
canonicalThielInvestmentAdviceComparison = thiel-investment-advice-comparison
  true true true true true false false

------------------------------------------------------------------------
-- Pareto: existence/interest is no longer the question; execution is.
------------------------------------------------------------------------

data PalantirInvestmentDebt : Set where
  exact2016MutualFundSellerIdentity : PalantirInvestmentDebt
  fiszelShareSellerIdentity : PalantirInvestmentDebt
  executedTradeOrSubscription : PalantirInvestmentDebt
  custodyAndPositionStatements : PalantirInvestmentDebt
  priceQuantityTerms : PalantirInvestmentDebt
  explicitDeclineOrExpiry : PalantirInvestmentDebt
  dispositionOrSale : PalantirInvestmentDebt
  inPersonAdviceMeeting : PalantirInvestmentDebt
  barakPalantirBoardProposal : PalantirInvestmentDebt

record PalantirInvestmentAcquisition : Set where
  constructor palantir-investment-acquisition
  field
    debt : PalantirInvestmentDebt
    priority : Nat
    sameObjectRequired : Bool
    instruction : String
open PalantirInvestmentAcquisition public

canonicalPalantirInvestmentAcquisition : List PalantirInvestmentAcquisition
canonicalPalantirInvestmentAcquisition =
  palantir-investment-acquisition executedTradeOrSubscription 100 true
    "Search brokerage, wire, subscription, cap-table and transfer-agent records for execution after the October 2016 mutual-fund offer or December 2016 Fiszel offer. Direct pricing negotiation substantially narrows the gap but does not close it."
  ∷ palantir-investment-acquisition custodyAndPositionStatements 100 true
    "Search Southern Trust/HBRK/Financial Trust and related portfolio/custody statements for a Palantir position; company research and 'hope you kept some stock' remain insufficient without a holding object."
  ∷ palantir-investment-acquisition exact2016MutualFundSellerIdentity 100 true
    "Resolve the mutual fund Thiel asked Epstein to identify, its selling vehicle, share class, transfer restrictions, quantity and whether the offer was accepted, renegotiated or allowed to expire."
  ∷ palantir-investment-acquisition fiszelShareSellerIdentity 99 true
    "Resolve the holder/vehicle behind Fiszel's December USD5-per-share access and whether it was the same seller/position as the October USD5.50 mutual-fund offer. Similar pricing and timing do not establish object identity."
  ∷ palantir-investment-acquisition explicitDeclineOrExpiry 99 true
    "Search follow-up correspondence for an explicit decline, expiry or decision not to buy; this can close the investment path without requiring a nonexistent trade record."
  ∷ palantir-investment-acquisition priceQuantityTerms 99 true
    "If an execution is found, resolve exact price, quantity, vehicle, beneficial owner, financing and seller separately."
  ∷ palantir-investment-acquisition dispositionOrSale 98 true
    "Trace any later sale/transfer/IPO conversion only after a holding is independently paid."
  ∷ palantir-investment-acquisition inPersonAdviceMeeting 97 true
    "Resolve Thiel's proposed later in-person Palantir discussion into a completed meeting/topic receipt without inferring completion from scheduling language."
  ∷ palantir-investment-acquisition barakPalantirBoardProposal 97 true
    "Resolve separately any Epstein-mediated Barak/Thiel Palantir board proposal or discussion from released audio/correspondence; proposal is not appointment."
  ∷ []
