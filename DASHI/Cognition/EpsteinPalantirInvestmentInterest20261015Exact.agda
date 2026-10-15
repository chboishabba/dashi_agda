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
-- This owner upgrades the previous shared-person-only boundary. Released
-- records pay direct Palantir investment inquiry/advice, a later secondary-
-- share opportunity routed to Epstein, and later valuation/company research.
-- They do not yet pay an executed purchase, custody position, beneficial
-- ownership, sale, board/governance right or Palantir corporate relationship.
------------------------------------------------------------------------

data InvestmentStage : Set where
  directInquiry : InvestmentStage
  directAdvice : InvestmentStage
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
  "Kahn and Epstein exchanged Palantir IPO/valuation material; the released corpus includes a detailed PitchBook Palantir profile generated for Kahn. Presence of research and an attachment named Palantir.pdf pays diligence/monitoring, not a stock custody statement or beneficial holding."
  true false false

record PalantirInvestmentBoundary : Set where
  constructor palantir-investment-boundary
  field
    directPalantirInvestmentInquiryPaid : Bool
    thielPalantirAdvicePaid : Bool
    secondaryShareOpportunityPaid : Bool
    laterCompanyDiligencePaid : Bool
    completedPurchasePaid : Bool
    custodyPositionPaid : Bool
    realisedSalePaid : Bool
    boardOrGovernanceRightPaid : Bool
    palantirCorporateClientRelationshipPaid : Bool
    valarInvestmentImpliesPalantirInvestment : Bool
open PalantirInvestmentBoundary public

canonicalPalantirInvestmentBoundary : PalantirInvestmentBoundary
canonicalPalantirInvestmentBoundary = palantir-investment-boundary
  true true true true false false false false false false

data InvestmentInquiryImpliesPurchase : Set where
data ShareOpportunityImpliesPurchase : Set where
data DiligenceImpliesCustodyPosition : Set where
data ValarLPImpliesPalantirHolding : Set where

directInquiryDoesNotCreatePurchase : InvestmentInquiryImpliesPurchase → ⊥
directInquiryDoesNotCreatePurchase ()

shareOpportunityDoesNotCreatePurchase : ShareOpportunityImpliesPurchase → ⊥
shareOpportunityDoesNotCreatePurchase ()

diligenceDoesNotCreateCustody : DiligenceImpliesCustodyPosition → ⊥
diligenceDoesNotCreateCustody ()

valarLPDoesNotCreatePalantirHolding : ValarLPImpliesPalantirHolding → ⊥
valarLPDoesNotCreatePalantirHolding ()

------------------------------------------------------------------------
-- Cross-pollination with the already-paid Thiel -> Valar investment path.
------------------------------------------------------------------------

record ThielInvestmentAdviceComparison : Set where
  constructor thiel-investment-advice-comparison
  field
    valarDirectSolicitationPaid : Bool
    southernTrustValarInvestmentCompleted : Bool
    palantirDirectAdvicePaid : Bool
    palantirSecondaryOpportunityPaid : Bool
    palantirInvestmentCompleted : Bool
    sameAdviserImpliesSameOutcome : Bool
open ThielInvestmentAdviceComparison public

canonicalThielInvestmentAdviceComparison : ThielInvestmentAdviceComparison
canonicalThielInvestmentAdviceComparison = thiel-investment-advice-comparison
  true true true true false false

------------------------------------------------------------------------
-- Pareto: existence/interest is no longer the question; execution is.
------------------------------------------------------------------------

data PalantirInvestmentDebt : Set where
  secondaryShareSellerIdentity : PalantirInvestmentDebt
  executedTradeOrSubscription : PalantirInvestmentDebt
  custodyAndPositionStatements : PalantirInvestmentDebt
  priceQuantityTerms : PalantirInvestmentDebt
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
    "Search brokerage, wire, subscription, cap-table and transaction records for an executed Epstein/Southern Trust/HBRK Palantir purchase after the 2014 inquiry or 2016 secondary-share offer."
  ∷ palantir-investment-acquisition custodyAndPositionStatements 100 true
    "Search portfolio/custody statements for a Palantir position; a Palantir.pdf attachment or PitchBook profile is not itself custody evidence."
  ∷ palantir-investment-acquisition secondaryShareSellerIdentity 99 true
    "Resolve who 'david' could access shares from, the seller/vehicle, transfer restrictions and whether the offer was accepted or declined."
  ∷ palantir-investment-acquisition priceQuantityTerms 99 true
    "If an execution is found, resolve exact price, quantity, vehicle, beneficial owner, valuation and financing separately."
  ∷ palantir-investment-acquisition dispositionOrSale 98 true
    "Trace any later sale/transfer/IPO conversion only after a holding is independently paid."
  ∷ palantir-investment-acquisition inPersonAdviceMeeting 97 true
    "Resolve Thiel's proposed later in-person Palantir discussion into a completed meeting/topic receipt without inferring completion from scheduling language."
  ∷ palantir-investment-acquisition barakPalantirBoardProposal 97 true
    "Resolve separately any Epstein-mediated Barak/Thiel Palantir board proposal or discussion from released audio/correspondence; proposal is not appointment."
  ∷ []
