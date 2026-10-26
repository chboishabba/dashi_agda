module DASHI.Cognition.EpsteinLiquidFundingOwnershipWinddownReceipt20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinLiquidFundingCrisisLineageBoundary20261014Exact as Prior

------------------------------------------------------------------------
-- LIQUID FUNDING OWNERSHIP / WIND-DOWN RECEIPT ROUND
--
-- Distinct questions:
--   * Bear Stearns's disclosed corporate interest;
--   * Financial Trust's Class A voting-unit interest in Holdings;
--   * operating repo/counterparty activity;
--   * March-April 2008 wind-down and liability satisfaction;
--   * 2011 consolidation of Class A voting units under Bear/JPM structure.
--
-- The source of the April 2008 liability payoff remains unresolved. Temporal
-- proximity to Bear/JPM/Fed rescue facilities does not itself establish that
-- Federal Reserve money paid Liquid Funding's liabilities.
------------------------------------------------------------------------

data LiquidSurface : Set where
  bearEquityInterest : LiquidSurface
  ftcVotingUnitInterest : LiquidSurface
  investmentManagement : LiquidSurface
  repoFacility : LiquidSurface
  ratedLiabilityWinddown : LiquidSurface
  counterpartyTermination : LiquidSurface
  votingUnitConsolidation : LiquidSurface
  ftcExitProceeds : LiquidSurface

record LiquidReceipt : Set where
  constructor liquid-receipt
  field
    label : String
    source : String
    boundedFinding : String
    surfaces : List LiquidSurface
    amountUSD : Nat
    primaryOrDirectCarrier : Bool
    federalBailoutAttributionPaid : Bool
open LiquidReceipt public

bear2002Disclosure : LiquidReceipt
bear2002Disclosure = liquid-receipt
  "Bear Stearns Liquid Funding interest"
  "Bear Stearns Companies FY2002 Form 10-K, SEC accession 0000914121-03-000238"
  "Bear Stearns disclosed an approximately 40% equity interest in Liquid Funding Ltd.; a Bear subsidiary acted as investment manager."
  (bearEquityInterest ∷ investmentManagement ∷ [])
  0 true false

jerFacilityReplacement : LiquidReceipt
jerFacilityReplacement = liquid-receipt
  "JER Liquid Funding repo replacement"
  "JER Investors Trust Form 8-K filed 1 Apr 2008, SEC accession 0001193125-08-072010"
  "JER disclosed that during March 2008 its Liquid Funding facility was replaced by a new Bear Stearns International repo facility with USD25m borrowing capacity. This pays an operating counterparty/wind-down coordinate, not a system-wide Liquid Funding liability amount."
  (repoFacility ∷ counterpartyTermination ∷ [])
  25000000 true false

moodyWinddownLocator : LiquidReceipt
moodyWinddownLocator = liquid-receipt
  "Liquid Funding rated-liability wind-down"
  "Moody's 18 Apr 2008 rating-withdrawal announcement, PR_153549, preserved by multiple contemporaneous/archival locators"
  "Moody's announced withdrawal of Liquid Funding ratings in connection with voluntary wind-down after payment and satisfaction in full of outstanding rated liabilities; it cited JPMorgan trustee reporting showing no rated debt outstanding as of 7 Apr and BNY Mellon reporting that Liquid Funding counterparty transactions had matured or terminated as of 8 Apr. The payoff funding source is not identified by this receipt."
  (ratedLiabilityWinddown ∷ counterpartyTermination ∷ [])
  0 false false

ftc2011SaleAgreement : LiquidReceipt
ftc2011SaleAgreement = liquid-receipt
  "Financial Trust Class A voting-unit sale"
  "EFTA00300182..201 / duplicate lineage including EFTA00284566 — Membership Interest Purchase and Sale Agreement dated 24 Mar 2011"
  "Financial Trust Company is a seller of Class A Voting Units in Liquid Funding Holdings LLC to Bear Stearns Liquid Funding Holdings Inc. The transaction was structured for the purchaser to acquire 100% of Class A Voting Units from all holders. The agreement also records Bear Stearns Bank plc, later J.P. Morgan Bank Dublin plc, as investment manager."
  (ftcVotingUnitInterest ∷ votingUnitConsolidation ∷ investmentManagement ∷ [])
  0 true false

ftcExitCredit : LiquidReceipt
ftcExitCredit = liquid-receipt
  "Financial Trust Liquid Funding exit credit"
  "EFTA01510050, Financial Trust JPMorgan statement, 31 Mar 2011"
  "Financial Trust's JPMorgan account records a USD265,303 credit associated with Bear Stearns Liquid Funding Holdings following the voting-unit sale. This pays the located FTC exit cash receipt; it does not identify FTC's percentage of all Class A units from the credit alone."
  (ftcExitProceeds ∷ [])
  265303 true false

record OwnershipWinddownBoundary : Set where
  constructor ownership-winddown-boundary
  field
    bearApprox40PercentInterestPaid : Bool
    ftcHeldClassAVotingUnitsPaid : Bool
    purchaserConsolidatedAllClassAUnitsPaid : Bool
    exactFTCOwnershipPercentagePaid : Bool
    liquidFundingOperatingCounterpartiesPaid : Bool
    april2008RatedLiabilitiesSatisfiedPaid : Bool
    exactLiabilityPayoffSourcePaid : Bool
    fedFacilityFundedLiquidFundingPayoffPaid : Bool
    bearRescueTemporalOverlapPaid : Bool
    temporalOverlapImpliesBailoutAttribution : Bool
open OwnershipWinddownBoundary public

canonicalOwnershipWinddownBoundary : OwnershipWinddownBoundary
canonicalOwnershipWinddownBoundary = ownership-winddown-boundary
  true true true false true true false false true false

data WinddownImpliesFedBailout : Set where
data BearOwnershipImpliesFullControl : Set where
data FTCVotingUnitsImpliesFortyPercentOwnership : Set where
data FullLiabilityPaymentImpliesPayoffSource : Set where

winddownDoesNotCreateFedBailout : WinddownImpliesFedBailout → ⊥
winddownDoesNotCreateFedBailout ()

bearOwnershipDoesNotCreateFullControl : BearOwnershipImpliesFullControl → ⊥
bearOwnershipDoesNotCreateFullControl ()

ftcVotingDoesNotCreateFortyPercentOwnership : FTCVotingUnitsImpliesFortyPercentOwnership → ⊥
ftcVotingDoesNotCreateFortyPercentOwnership ()

liabilityPaymentDoesNotCreatePayoffSource : FullLiabilityPaymentImpliesPayoffSource → ⊥
liabilityPaymentDoesNotCreatePayoffSource ()

------------------------------------------------------------------------
-- Max-cut: cap table and 2008 cash source, not generic bailout rhetoric.
------------------------------------------------------------------------

data LiquidDebt : Set where
  holdingsLLCCapTable : LiquidDebt
  april2008PayoffSource : LiquidDebt
  trusteeOutstandingReports : LiquidDebt
  liquidationCashflowLedger : LiquidDebt
  ftcOriginalSubscriptionCost : LiquidDebt
  classARightsAndEconomics : LiquidDebt
  maidenLaneAssetIntersection : LiquidDebt

record LiquidAcquisition : Set where
  constructor liquid-acquisition
  field
    debt : LiquidDebt
    priority : Nat
    question : String
open LiquidAcquisition public

canonicalLiquidAcquisition : List LiquidAcquisition
canonicalLiquidAcquisition =
  liquid-acquisition april2008PayoffSource 100
    "Acquire Liquid Funding's March-April 2008 cashflow/liability ledger and identify the actual sources used to satisfy outstanding rated liabilities; do not infer a Fed source from rescue timing." ∷
  liquid-acquisition holdingsLLCCapTable 100
    "Acquire the Liquid Funding Holdings LLC Class A/Class B cap table and amendments to resolve Financial Trust's exact voting/economic percentage and the relationship to Bear's disclosed approximately 40% Liquid Funding Ltd interest." ∷
  liquid-acquisition trusteeOutstandingReports 99
    "Acquire the cited JPMorgan 7-Apr-2008 Outstanding Detail Report and BNY Mellon 8-Apr-2008 Program Outstanding Report as direct payoff/termination carriers." ∷
  liquid-acquisition liquidationCashflowLedger 99
    "Reconstruct asset sales, repo unwinds, swap terminations, note/commercial-paper repayments and residual equity distributions across the wind-down." ∷
  liquid-acquisition classARightsAndEconomics 98
    "Resolve voting, distribution, liquidation and transfer rights attached to Class A Voting Units under the 2001 LLC agreement." ∷
  liquid-acquisition ftcOriginalSubscriptionCost 98
    "Acquire Financial Trust's initial/subsequent Class A acquisition cost and distributions so the USD265,303 2011 exit receipt can be interpreted economically." ∷
  liquid-acquisition maidenLaneAssetIntersection 97
    "Test exact asset/security identifiers against Maiden Lane/Bear rescue schedules; shared mortgage-asset class or timing is not enough to attribute the payoff to Maiden Lane/Fed support." ∷
  []
