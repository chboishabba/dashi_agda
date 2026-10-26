module DASHI.Cognition.SystemicPowerInfrastructurePareto20261016Round4Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.SystemicPowerInfrastructurePareto20261016Round3Exact as Prior
import DASHI.Cognition.BlackRockCrisisBenefitOrderLedger20261016Exact as Benefits

------------------------------------------------------------------------
-- SYSTEMIC POWER INFRASTRUCTURE PARETO — ROUND 4, 2026-10-16
--
-- Round 4 promotes effect-order incidence itself. The crisis intervention is
-- no longer represented as a binary bailout/not-bailout edge: direct capital,
-- public contracts, loss avoidance, mark-to-market support, homeowner relief,
-- institutional learning, scale, future-selection option value and durable
-- public-private capacity are separately typed.
------------------------------------------------------------------------

data Lane4 : Set where
  crisisOrderedBenefitIncidence : Lane4
  privateExpertiseStateCapacityFeedback : Lane4
  homeownerAssetHolderTemporalIncidence : Lane4
  postCrisisAssetManagerScaleTopology : Lane4
  nineBankManagerBeneficialOwnership : Lane4
  crisisPublicReturnAndRiskIncidence : Lane4
  priorSystemicFront : Lane4

record Profile4 : Set where
  constructor profile4
  field
    lane : Lane4
    priority : Nat
    firstOrderEvidenceHigh : Bool
    secondOrderLeverageHigh : Bool
    thirdOrderLeverageHigh : Bool
    beneficiaryResolutionDebtHigh : Bool
    reading : String
open Profile4 public

canonicalFront4 : List Profile4
canonicalFront4 =
  profile4 crisisOrderedBenefitIncidence 100 true true true true
    "The crisis ledger now separates institution-level preferred capital, BlackRock public mandates, public preferred/residual returns, later homeowner relief, creditor/counterparty tail-risk reduction, security-holder mark-to-market effects and manager/client exposure. The max-cut is beneficial-owner and magnitude resolution, not deciding that one actor was 'the beneficiary'." ∷
  profile4 privateExpertiseStateCapacityFeedback 100 true true true true
    "BlackRock's 2008 Maiden Lane implementation and 2020 New York Fed reselection create a literal repeated-crisis-role sequence. The third-order question is whether implementation experience, relationships, models/data and operational infrastructure create measurable future-selection advantage or public dependence; repetition alone does not prove capture." ∷
  profile4 homeownerAssetHolderTemporalIncidence 100 true true true true
    "Financial-institution support was immediate in October 2008 while major TARP homeowner relief arrived later and had different scale/reach. The strong question is temporal and distributional incidence across security holders, creditors, homeowners, renters, workers and taxpayers, not the false claim that homeowner programmes did not exist." ∷
  profile4 postCrisisAssetManagerScaleTopology 99 true true true true
    "BlackRock's 2009 BGI transaction produced a paid scale discontinuity to USD3.346tn AUM, while Bank of America/Merrill, PNC and Barclays held large BlackRock capital positions. This is concrete reciprocal capital topology after the crisis; public crisis mandates are not promoted to causes of the BGI acquisition or asset inflows." ∷
  profile4 nineBankManagerBeneficialOwnership 99 false true true true
    "The viral 'eight of nine' claim remains unresolved. The relevant object is announcement-date holding-by-holding exposure across BlackRock-managed vehicles and Larry Fink personal holdings, separated from the large bank ownership stakes in BlackRock itself after the BGI transaction." ∷
  profile4 crisisPublicReturnAndRiskIncidence 99 true true true true
    "Treasury CPP securities carried dividends/protective terms and Maiden Lane repayment waterfalls could return gains to the public, while taxpayers/public institutions bore downside and liquidity risk. Intervention therefore requires a two-sided public return/risk ledger rather than a one-way-transfer model." ∷
  profile4 priorSystemicFront 100 true true true true
    "Palantir state-capacity/contestability, banking and elite access, private-capital housing-AI-power assetisation, Black/Apollo/Valar/Wexner/Bear and Springfield value-incidence remain co-frontier lanes. Crisis-state finance supplies a reusable E1/E2/E3 benefit grammar rather than displacing those objects."
  ∷ []

record Boundary4 : Set where
  constructor boundary4
  field
    firstOrderGainDeterminesSecondOrderGain : Bool
    secondOrderGainDeterminesThirdOrderPower : Bool
    beneficiaryImpliesMotive : Bool
    beneficiaryImpliesCrisisAuthorship : Bool
    adviserImpliesRecipientSelection : Bool
    managedAssetsImpliesManagerOwnership : Bool
    repeatedMandatesImpliesCapture : Bool
    postCrisisScaleImpliesBailoutCausation : Bool
    assetPriceSupportImpliesUniformInflationBenefit : Bool
    publicReturnErasesPublicRisk : Bool
open Boundary4 public

canonicalBoundary4 : Boundary4
canonicalBoundary4 = boundary4
  false false false false false false false false false false

data FirstOrderDeterminesSecondOrder : Set where
data SecondOrderDeterminesThirdOrder : Set where
data BenefitImpliesMotive : Set where
data ScaleImpliesBailoutCausation : Set where
data InflationImpliesUniformAssetGain : Set where

firstOrderDoesNotDetermineSecondOrder : FirstOrderDeterminesSecondOrder → ⊥
firstOrderDoesNotDetermineSecondOrder ()

secondOrderDoesNotDetermineThirdOrder : SecondOrderDeterminesThirdOrder → ⊥
secondOrderDoesNotDetermineThirdOrder ()

benefitDoesNotCreateMotive : BenefitImpliesMotive → ⊥
benefitDoesNotCreateMotive ()

scaleDoesNotCreateBailoutCausation : ScaleImpliesBailoutCausation → ⊥
scaleDoesNotCreateBailoutCausation ()

inflationDoesNotCreateUniformAssetGain : InflationImpliesUniformAssetGain → ⊥
inflationDoesNotCreateUniformAssetGain ()

------------------------------------------------------------------------
-- Terminal max-cut after ordered-benefit promotion.
------------------------------------------------------------------------

data Debt4 : Set where
  nineCPPBeneficialOwnerSnapshots : Debt4
  cppClaimClassRecoveryLedger : Debt4
  blackRockMaidenLaneFeesConflicts : Debt4
  homeownerInstitutionTimingReachLedger : Debt4
  mandateCapabilityReselectionJoin : Debt4
  fed2020CUSIPBeneficiaryMap : Debt4
  publicPrivateCapabilityConcentration : Debt4
  blackRockBGICausalBoundary : Debt4

data IncidenceOrder : Set where
  E1 : IncidenceOrder
  E2 : IncidenceOrder
  E3 : IncidenceOrder

record Acquisition4 : Set where
  constructor acquisition4
  field
    debt : Debt4
    priority : Nat
    effectOrder : IncidenceOrder
    instruction : String
open Acquisition4 public

canonicalAcquisition4 : List Acquisition4
canonicalAcquisition4 =
  acquisition4 nineCPPBeneficialOwnerSnapshots 100 E2
    "Resolve October-2008 holdings of common/preferred/debt claims in each of the nine initial CPP institutions by beneficial owner and manager; separately resolve Larry Fink personal positions and BlackRock-managed client positions." ∷
  acquisition4 cppClaimClassRecoveryLedger 100 E2
    "Measure direct cash, avoided default loss and mark-to-market recovery by claim class across CPP institutions; do not treat shareholders, creditors, depositors and counterparties as one beneficiary class." ∷
  acquisition4 homeownerInstitutionTimingReachLedger 100 E2
    "Join immediate institution support and later homeowner relief on common timing, committed/disbursed amount, eligibility, reach, foreclosure avoidance and recovery coordinates." ∷
  acquisition4 mandateCapabilityReselectionJoin 100 E3
    "Join BlackRock's 2008 and 2020 public mandates by personnel, models/data, procurement rationale, operational capability and subsequent selection to test the expertise->mandate->learning->reselection feedback loop without assuming capture." ∷
  acquisition4 blackRockMaidenLaneFeesConflicts 99 E1
    "Extract fee letters, client security exposures and conflict-management provisions for ML I/II/III so BlackRock's direct contractual benefit and any same-security conflict surfaces are quantified." ∷
  acquisition4 fed2020CUSIPBeneficiaryMap 99 E2
    "Use published transaction/CUSIP data and holder snapshots to distinguish sellers receiving cash, holders receiving spread/price effects, issuers receiving financing-option benefits and managers receiving fee/AUM effects." ∷
  acquisition4 publicPrivateCapabilityConcentration 99 E3
    "Measure market share, competing-vendor access, public internal modelling capacity, data/model ownership and switching costs across crisis mandates; repeated use is not automatically capture." ∷
  acquisition4 blackRockBGICausalBoundary 97 E3
    "Retain the paid BGI scale/ownership topology while searching for actual evidence linking public crisis work to the transaction, client flows or acquisition financing; chronology alone cannot pay causation."
  ∷ []
