module DASHI.Cognition.EpsteinValarLPMechanics20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinSouthernTrustInvestmentFlowAtlas20261014Exact as Flow

------------------------------------------------------------------------
-- SOUTHERN TRUST / VALAR LP ECONOMIC MECHANICS
--
-- This owner distinguishes Southern Trust's LP capital from the economics and
-- governance retained by Valar's GP/founding partners. LP participation does
-- not imply portfolio-company control or a bilateral Epstein-Thiel operation.
------------------------------------------------------------------------

record ValarFundTerms : Set where
  constructor valar-fund-terms
  field
    fundLabel : String
    targetSizeUSD : Nat
    termYears : Nat
    commitmentPeriodYears : Nat
    managementFeeBpsInitial : Nat
    carriedInterestFirstTierPct : Nat
    carriedInterestSecondTierPct : Nat
    carriedInterestThirdTierPct : Nat
    source : String
open ValarFundTerms public

fundIIITerms : ValarFundTerms
fundIIITerms = valar-fund-terms
  "Valar Global Fund III LP"
  200000000 10 5 250 20 25 30
  "EFTA00609489 Valar Fund III PPM"

record ThielEconomicControl : Set where
  constructor thiel-economic-control
  field
    generalPartnerMembershipPaid : Bool
    shareOfCarryPct : Nat
    shareOfNetManagementFeesPct : Nat
    vetoRightsPaid : Bool
    vetoScope : String
    directControlOfSouthernTrustPaid : Bool
open ThielEconomicControl public

canonicalThielEconomicControl : ThielEconomicControl
canonicalThielEconomicControl = thiel-economic-control
  true 20 20 true
  "PPM states veto rights over specified GP/Fund matters including Investment Committee composition, certain conflict investments, Advisory Committee-consent actions and material partner deadlocks."
  false

record SouthernTrustValarPosition : Set where
  constructor southern-trust-valar-position
  field
    fundIICommitmentUSD : Nat
    fundIIICommitmentUSD : Nat
    combinedCommitmentUSD : Nat
    fundIIICommitmentRelativeToTargetPctApprox : Nat
    limitedPartnerPaid : Bool
    paidInCapitalPaid : Bool
    portfolioCompanyControlPaid : Bool
    specialSideLetterPaid : Bool
open SouthernTrustValarPosition public

canonicalSouthernTrustValarPosition : SouthernTrustValarPosition
canonicalSouthernTrustValarPosition = southern-trust-valar-position
  15000000 25000000 40000000 12 true true false false

record ValarEconomicBridge : Set where
  constructor valar-economic-bridge
  field
    southernTrustCapitalPaysFundFees : Bool
    southernTrustCapitalParticipatesInNetReturns : Bool
    thielEconomicParticipationInFundPaid : Bool
    southernTrustLPImpliesThielPersonalPayment : Bool
    lpRelationshipImpliesCommonPoliticalPurpose : Bool
open ValarEconomicBridge public

canonicalValarEconomicBridge : ValarEconomicBridge
canonicalValarEconomicBridge = valar-economic-bridge
  true true true false false

data LPImpliesPortfolioControl : Set where
data LPImpliesPoliticalCoordination : Set where
data FundFeesImpliesDirectPersonalPayment : Set where

lpDoesNotCreatePortfolioControl : LPImpliesPortfolioControl → ⊥
lpDoesNotCreatePortfolioControl ()

lpDoesNotCreatePoliticalCoordination : LPImpliesPoliticalCoordination → ⊥
lpDoesNotCreatePoliticalCoordination ()

fundFeesDoNotCreateDirectPersonalPayment : FundFeesImpliesDirectPersonalPayment → ⊥
fundFeesDoNotCreateDirectPersonalPayment ()

------------------------------------------------------------------------
-- Pareto acquisition after paying the generic LP mechanics.
------------------------------------------------------------------------

data ValarDebt : Set where
  exactFundIIILPA : ValarDebt
  southernTrustSubscriptionAgreement : ValarDebt
  southernTrustSideLetters : ValarDebt
  distributionLedger : ValarDebt
  estateDisposition : ValarDebt
  underlyingPortfolioExposure : ValarDebt

record ValarAcquisition : Set where
  constructor valar-acquisition
  field
    debt : ValarDebt
    priority : Nat
    question : String
open ValarAcquisition public

canonicalValarAcquisition : List ValarAcquisition
canonicalValarAcquisition =
  valar-acquisition southernTrustSubscriptionAgreement 100
    "Acquire Southern Trust's executed Fund II and Fund III subscription agreements and acceptance pages to resolve investor-specific representations, rights and dates."
  ∷ valar-acquisition southernTrustSideLetters 100
    "Search for any Southern Trust-specific side letter, fee concession, advisory-committee right, co-investment right or information right; absence must not be assumed from the generic PPM."
  ∷ valar-acquisition distributionLedger 99
    "Reconstruct actual distributions, recycling and realised proceeds separately from capital-account/valuation estimates."
  ∷ valar-acquisition exactFundIIILPA 99
    "Acquire the executed Fund III partnership agreement controlling over the PPM summary and resolve LP amendment/consent mechanics."
  ∷ valar-acquisition estateDisposition 98
    "Resolve the 2019-2026 estate treatment, extensions, liquidation and final disposition of the Valar II/III interests."
  ∷ valar-acquisition underlyingPortfolioExposure 97
    "Map Southern Trust's economic exposure through Valar to underlying companies without treating LP status as direct ownership/control of each company."
  ∷ []
