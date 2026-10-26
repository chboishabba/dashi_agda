module DASHI.Cognition.EpsteinWexnerCOUQFungibleCapitalLifecycle20261015Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinFinancialTrustBearCrisisAwarenessSettlement20261014Exact as Bear
import DASHI.Cognition.EpsteinWexnerChildrenTrustCapitalMesh20261015Exact as Wexner

------------------------------------------------------------------------
-- WEXNER -> C.O.U.Q. FUNGIBLE CAPITAL LIFECYCLE — 2026-10-15
--
-- The source-paid object is capitalisation of a foundation associated with
-- Epstein and the foundation's later investments/dispositions. Contributions
-- increase the foundation's fungible capital pool. They do not establish that
-- a particular donor's specific dollars/shares funded a later investment.
------------------------------------------------------------------------

data COUQSurface : Set where
  wexnerChildrenTrustContribution : COUQSurface
  wexnerCharitableFundContribution : COUQSurface
  epsteinFoundationOfficer : COUQSurface
  bearABSInvestment : COUQSurface
  ylkAssignment : COUQSurface
  charitableGranting : COUQSurface

record COUQReceipt : Set where
  constructor couq-receipt
  field
    label : String
    dateOrYear : String
    source : String
    boundedFinding : String
    amountOrValueUSD : Nat
    surfaces : List COUQSurface
    paid : Bool
open COUQReceipt public

wexnerChildrenTrustGift2002 : COUQReceipt
wexnerChildrenTrustGift2002 = couq-receipt
  "Wexner Children's Trust stock contribution to C.O.U.Q."
  "FY ending 2002-02-28"
  "C.O.U.Q. Foundation Form 990-PF, EFTA00192401 / EFTA00224323"
  "The foundation's filed return records a contribution from Leslie H. Wexner, as grantor of The Wexner Children's Trust, of 600,000 Too, Inc. common shares with USD11.205m market value at the gift date, recorded on the foundation's books at donor basis. Market value and tax/book basis are distinct coordinates."
  11205000 (wexnerChildrenTrustContribution ∷ []) true

wexnerCharitableFundGift2003 : COUQReceipt
wexnerCharitableFundGift2003 = couq-receipt
  "Leslie H. Wexner Charitable Fund contribution to C.O.U.Q."
  "2003 Schedule B filing"
  "C.O.U.Q. Foundation Schedule B / EFTA00224355 and duplicate tax-return bundle"
  "The filed Schedule B names The Leslie H. Wexner Charitable Fund as contributor of USD10m to The C.O.U.Q. Foundation. This is a foundation-level contribution receipt; it does not state a downstream investment purpose."
  10000000 (wexnerCharitableFundContribution ∷ []) true

couqEpsteinOfficerSurface : COUQReceipt
couqEpsteinOfficerSurface = couq-receipt
  "C.O.U.Q. Epstein officer/director surface"
  "tax-return and corporate-record period"
  "C.O.U.Q. Form 990-PF corpus / EFTA00192298-EFTA002243xx; 2008 corporate record EFTA00192304"
  "Released C.O.U.Q. tax/corporate records identify Jeffrey Epstein as president/director and Darren Indyke in officer/director roles. This pays formal governance association, not personal beneficial ownership of every foundation asset."
  0 (epsteinFoundationOfficer ∷ []) true

couqBearABS2004 : COUQReceipt
couqBearABS2004 = couq-receipt
  "C.O.U.Q. Bear ABS contribution"
  "2004-01"
  "2011 Bear settlement schedule, EFTA00611329 / EFTA00597989"
  "The settlement schedule records a USD10m C.O.U.Q. contribution to the Bear Stearns Asset Backed Securities investment family in January 2004. This pays foundation investment deployment separately from prior donor contributions."
  10000000 (bearABSInvestment ∷ []) true

couqToYLK2008 : COUQReceipt
couqToYLK2008 = couq-receipt
  "C.O.U.Q. assigns Bear ABS interest to YLK Charitable Trust"
  "2008-01-01"
  "Bear settlement schedule/recital, EFTA00611329"
  "The settlement record states that C.O.U.Q. assigned 100% of the shares it owned in Bear Stearns Asset Backed Securities Overseas, Ltd. to YLK Charitable Trust under a January 1, 2008 instrument. The record pays transfer of the investment interest, not the beneficial ownership or purpose of YLK."
  0 (ylkAssignment ∷ bearABSInvestment ∷ []) true

record COUQCapitalPoolBoundary : Set where
  constructor couq-capital-pool-boundary
  field
    wexnerVehicleContributionsPaid : Bool
    combinedNominalContributionValueUSD : Nat
    couqEpsteinGovernanceAssociationPaid : Bool
    couqBearInvestmentPaid : Bool
    couqYLKAssignmentPaid : Bool
    contributionsIncreaseCOUQCapitalCapacity : Bool
    wexnerSpecificContributionEarmarkedToBearPaid : Bool
    donorContributionImpliesDonorControlOfLaterInvestment : Bool
    foundationOfficerImpliesPersonalBeneficialOwnership : Bool
    ylkTransferPurposePaid : Bool
open COUQCapitalPoolBoundary public

canonicalCOUQCapitalPoolBoundary : COUQCapitalPoolBoundary
canonicalCOUQCapitalPoolBoundary = couq-capital-pool-boundary
  true 21205000 true true true true false false false false

data FungibleContributionImpliesEarmarkedInvestment : Set where
data DonationImpliesDownstreamControl : Set where
data FoundationOfficeImpliesBeneficialOwnership : Set where

giftDoesNotCreateEarmarking : FungibleContributionImpliesEarmarkedInvestment → ⊥
giftDoesNotCreateEarmarking ()

donationDoesNotCreateDownstreamControl : DonationImpliesDownstreamControl → ⊥
donationDoesNotCreateDownstreamControl ()

officeDoesNotCreateBeneficialOwnership : FoundationOfficeImpliesBeneficialOwnership → ⊥
officeDoesNotCreateBeneficialOwnership ()

------------------------------------------------------------------------
-- Max-cut: governing instruments and full inflow/outflow incidence.
------------------------------------------------------------------------

data COUQDebt : Set where
  completeDonorLedger : COUQDebt
  completeGrantLedger : COUQDebt
  foundationGoverningInstrument : COUQDebt
  investmentPolicyAndAuthority : COUQDebt
  ylkTrustInstrumentAndBeneficiaries : COUQDebt
  wexnerTrustGiftAuthorization : COUQDebt
  charitableFundGiftAuthorization : COUQDebt
  bearInvestmentDecisionRecords : COUQDebt

record COUQAcquisition : Set where
  constructor couq-acquisition
  field
    debt : COUQDebt
    priority : Nat
    sameObjectRequired : Bool
    question : String
open COUQAcquisition public

canonicalCOUQAcquisition : List COUQAcquisition
canonicalCOUQAcquisition =
  couq-acquisition foundationGoverningInstrument 100 true
    "Acquire C.O.U.Q. charter/bylaws/trustee resolutions and investment-authority rules to distinguish formal officer status, board authority and beneficial/public-purpose constraints."
  ∷ couq-acquisition completeDonorLedger 100 true
    "Reconcile all filed contributions by year, donor vehicle, cash/noncash form and tax/book value rather than treating the two Wexner receipts as the foundation's entire capital base."
  ∷ couq-acquisition completeGrantLedger 99 true
    "Reconstruct C.O.U.Q. grants and investment distributions by date and purpose to measure who captured or received foundation value after capitalisation."
  ∷ couq-acquisition ylkTrustInstrumentAndBeneficiaries 99 true
    "Resolve YLK Charitable Trust settlor/trustees/beneficiaries and the economic reason for the 2008 ABS-interest assignment."
  ∷ couq-acquisition investmentPolicyAndAuthority 98 true
    "Acquire resolutions/adviser records for Bear and other investments to identify who selected investments and under what mandate."
  ∷ couq-acquisition wexnerTrustGiftAuthorization 98 true
    "Acquire the Wexner Children's Trust instrument/resolution authorising the 600,000-share contribution and identify the exact trust/legal authority involved."
  ∷ couq-acquisition charitableFundGiftAuthorization 98 true
    "Acquire governing approval for the USD10m Wexner Charitable Fund contribution and the donor-fund trustee decision surface."
  ∷ couq-acquisition bearInvestmentDecisionRecords 97 true
    "Join the 2004 Bear investment to C.O.U.Q. board/adviser decision records; fungible capital capacity does not require donor-dollar tracing."
  ∷ []
