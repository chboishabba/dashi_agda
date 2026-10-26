module DASHI.Cognition.SystemicPowerInfrastructurePareto20261016Round5Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.SystemicPowerInfrastructurePareto20261016Round4Exact as Prior
import DASHI.Cognition.BlackRockCrisisAcquisitionReceiptRound20261016Exact as CrisisRound

------------------------------------------------------------------------
-- SYSTEMIC POWER INFRASTRUCTURE PARETO — ROUND 5, 2026-10-16
--
-- New payments:
--   * Fink advice existed, but his stated troubled-asset recommendation diverged
--     from Paulson's implemented bank-equity strategy;
--   * Merrill Lynch, an initial CPP recipient, owned ~48.2% of BlackRock's
--     fully diluted capital at end-2008; Bank of America inherited the position;
--   * by Sep-2010 direct CPP disbursement (~USD204.9bn) dwarfed TARP housing
--     disbursement (~USD543m), paying temporal/scale incidence;
--   * CPP ultimately returned substantial principal/income to Treasury;
--   * the 2020 BlackRock corporate-credit mandate has exact fee and affiliated-
--     ETF revenue-credit/conflict-mitigation receipts, and BlackRock acted under
--     New York Fed guidelines rather than owning monetary-policy authority.
------------------------------------------------------------------------

data Lane5 : Set where
  advisoryInfluenceVersusDecisionAuthority : Lane5
  reciprocalBankAssetManagerOwnershipTopology : Lane5
  institutionHouseholdTemporalDistribution : Lane5
  publicRiskReturnLedger : Lane5
  crisisVendorConflictAndFeeIncidence : Lane5
  crisisMandateReselectionStateCapacity : Lane5
  nineBankBlackRockManagedExposure : Lane5
  ccfSecurityBeneficiaryIncidence : Lane5
  priorFront : Lane5

record Profile5 : Set where
  constructor profile5
  field
    lane : Lane5
    priority : Nat
    firstOrderPaid : Bool
    secondOrderPaid : Bool
    thirdOrderPaid : Bool
    remainingDebtHigh : Bool
    reading : String
open Profile5 public

canonicalFront5 : List Profile5
canonicalFront5 =
  profile5 advisoryInfluenceVersusDecisionAuthority 100 true true true false
    "Fink had crisis-period advisory access, but his reported recommendation to use TARP to purchase troubled assets diverged from Paulson's implemented preferred-equity bank capital programme. Advice/influence is therefore paid while sovereign policy authorship and recipient selection remain blocked." ∷
  profile5 reciprocalBankAssetManagerOwnershipTopology 100 true true false true
    "At end-2008 Merrill Lynch held about 48.2% of BlackRock fully diluted capital and was itself an initial CPP recipient. Bank of America acquired Merrill on 1 Jan 2009 and inherited a very large BlackRock economic position. The live question is the value/incidence of that reciprocal topology, not a simplistic 'BlackRock owned the bailed banks' narrative." ∷
  profile5 institutionHouseholdTemporalDistribution 100 true true false true
    "By Sep-2010 CPP had disbursed about USD204.9bn while TARP housing programmes had disbursed about USD543m. Homeowner aid existed, but the timing and scale asymmetry is now source-paid and should be joined to foreclosure, credit and employment outcomes rather than compressed into 'no homeowner help'." ∷
  profile5 publicRiskReturnLedger 99 true true false true
    "CPP was not a one-way cash gift: about USD204.9bn was invested and Treasury later reported roughly USD226.77bn in repayments/income by Sep-2019. Financial recovery does not erase distributional, opportunity or crisis externalities, but it changes the incidence ledger materially." ∷
  profile5 crisisVendorConflictAndFeeIncidence 100 true true false true
    "The 2020 SMCCF mandate now has exact gross BlackRock advisory fees and affiliated-ETF revenue credits. The conflict surface was real and contractually mitigated; BlackRock acted at the New York Fed's sole direction. The remaining cut is comparable Maiden Lane fee/client-exposure detail and security-level beneficiary incidence." ∷
  profile5 crisisMandateReselectionStateCapacity 100 true true false true
    "2008 and 2020 public crisis roles now form a repeated-mandate sequence with official 2020 selection rationale based on expertise and operational capability. The third-order question remains whether earlier public work produced measurable later selection advantage, model/data concentration or public dependency." ∷
  profile5 nineBankBlackRockManagedExposure 99 false false false true
    "The viral 'eight of nine' proposition is still not paid. It requires a dated manager-level holdings matrix across all nine initial CPP institutions and a separate Larry Fink personal-beneficial-ownership surface. Reverse ownership by Merrill/Bank of America is paid and should not be confused with this question." ∷
  profile5 ccfSecurityBeneficiaryIncidence 99 true false false true
    "The 2020 facilities' maximum size, actual purchases, vendor role and conflict controls are paid, but direct sellers, contemporaneous holders, spread beneficiaries and issuer financing-option gains still require CUSIP/ETF-level ownership and transaction mapping." ∷
  profile5 priorFront 100 true true true true
    "Palantir/TIA state-capacity, Epstein/Black/Apollo/Valar/Wexner/Bear banking, housing-AI-power assetisation and Springfield value capture remain co-frontier. This round adds a reusable crisis-finance incidence pattern: advice != authority; direct support != downstream gain; repeated public mandates can create third-order capability/selection questions."
  ∷ []

record Boundary5 : Set where
  constructor boundary5
  field
    adviceEqualsImplementedPolicy : Bool
    bankOwnershipOfBlackRockEqualsBlackRockOwnershipOfBank : Bool
    bailoutRecipientOwnershipImpliesSelfSelection : Bool
    publicFinancialRecoveryEqualsDistributionalNeutrality : Bool
    vendorFeeEqualsPolicyAuthority : Bool
    conflictMitigationEqualsNoConflict : Bool
    repeatedMandateEqualsCapture : Bool
    maxFacilityCapacityEqualsMoneyPrintedOrSpent : Bool
open Boundary5 public

canonicalBoundary5 : Boundary5
canonicalBoundary5 = boundary5 false false false false false false false false

data AdviceImpliesPolicy : Set where
data ReverseOwnershipImpliesForwardOwnership : Set where
data RecoveryImpliesNeutrality : Set where
data VendorFeeImpliesAuthority : Set where
data MitigatedConflictImpliesNoConflict : Set where
data RepeatMandateImpliesCapture : Set where

adviceDoesNotCreatePolicy : AdviceImpliesPolicy → ⊥
adviceDoesNotCreatePolicy ()

reverseOwnershipDoesNotCreateForwardOwnership : ReverseOwnershipImpliesForwardOwnership → ⊥
reverseOwnershipDoesNotCreateForwardOwnership ()

recoveryDoesNotCreateNeutrality : RecoveryImpliesNeutrality → ⊥
recoveryDoesNotCreateNeutrality ()

vendorFeeDoesNotCreateAuthority : VendorFeeImpliesAuthority → ⊥
vendorFeeDoesNotCreateAuthority ()

mitigationDoesNotEraseConflictSurface : MitigatedConflictImpliesNoConflict → ⊥
mitigationDoesNotEraseConflictSurface ()

repeatMandateDoesNotCreateCapture : RepeatMandateImpliesCapture → ⊥
repeatMandateDoesNotCreateCapture ()

------------------------------------------------------------------------
-- Max-cut after Round 5 acquisition.
------------------------------------------------------------------------

data Debt5 : Set where
  nineBankManagerHoldingsMatrix : Debt5
  finkPersonalBeneficialOwnership : Debt5
  reverseOwnershipValueRealisation : Debt5
  maidenLaneFeeClientConflictLedger : Debt5
  ccfCUSIPHolderSellerMap : Debt5
  crisisMandateCapabilityCausalJoin : Debt5
  homeownerInstitutionOutcomeCounterfactual : Debt5
  crisisPolicyAssetHolderDistribution : Debt5

record Acquisition5 : Set where
  constructor acquisition5
  field
    debt : Debt5
    priority : Nat
    effectOrder : Prior.IncidenceOrder
    instruction : String
open Acquisition5 public

canonicalAcquisition5 : List Acquisition5
canonicalAcquisition5 =
  acquisition5 nineBankManagerHoldingsMatrix 100 Prior.E2
    "Build a dated October-2008 matrix for BlackRock-managed common/debt holdings in each initial CPP institution. Only then test the 'eight of nine' statement, and keep management, delegated voting and beneficial ownership separate." ∷
  acquisition5 finkPersonalBeneficialOwnership 100 Prior.E2
    "Resolve Larry Fink's personal holdings in the nine institutions from disclosures/transaction records; do not infer them from BlackRock client AUM." ∷
  acquisition5 reverseOwnershipValueRealisation 100 Prior.E2
    "Quantify Merrill/Bank of America's ~48.2%/~47.4% BlackRock economic position using dated BLK values, dividends, exchanges and later sales to measure second-order gain/loss on the paid reverse-ownership path." ∷
  acquisition5 maidenLaneFeeClientConflictLedger 99 Prior.E1
    "Recover BlackRock's Maiden Lane I/II/III fee schedules and same-security client exposures/conflict controls, using the 2020 CCF fee/credit treatment as a comparator rather than assuming identical terms." ∷
  acquisition5 ccfCUSIPHolderSellerMap 99 Prior.E2
    "Map 2020 Fed CUSIP/ETF purchases to sellers, contemporaneous holders and issuers, separating direct cash sale, spread compression, mark-to-market and financing-option benefit." ∷
  acquisition5 crisisMandateCapabilityCausalJoin 99 Prior.E3
    "Test the expertise->public mandate->learning/data/model capability->reselection hypothesis using staff, model/data, procurement rationale and competing-bid evidence across 2008 and 2020." ∷
  acquisition5 homeownerInstitutionOutcomeCounterfactual 98 Prior.E3
    "Move from paid cash-flow timing asymmetry to credible causal estimates of foreclosure avoidance, credit supply, unemployment, wealth effects and public recovery under alternative interventions." ∷
  acquisition5 crisisPolicyAssetHolderDistribution 98 Prior.E3
    "Resolve asset-price and inflation incidence by security class, leverage, liabilities and beneficial owner; 'asset holders benefit' is too coarse for third-order distributional analysis."
  ∷ []
