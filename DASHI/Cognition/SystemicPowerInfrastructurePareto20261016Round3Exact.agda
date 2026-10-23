module DASHI.Cognition.SystemicPowerInfrastructurePareto20261016Round3Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.SystemicPowerInfrastructurePareto20261015Round2Exact as Prior
import DASHI.Cognition.BlackRockFinkCrisisStateAdvisoryIncidence20261016Exact as Crisis

------------------------------------------------------------------------
-- SYSTEMIC POWER INFRASTRUCTURE PARETO — ROUND 3, 2026-10-16
--
-- New lane: repeated private-finance expertise -> public crisis advisory /
-- implementation -> distributional incidence -> possible durable private-public
-- infrastructure. The compressed social-media narrative is decomposed so that
-- CMO/CDO, advice/decision authority, AUM/personal ownership and institutional /
-- homeowner support are never collapsed.
------------------------------------------------------------------------

data Lane3 : Set where
  crisisStateFinancialAdvisoryInfrastructure : Lane3
  crisisDistributionalIncidence : Lane3
  blackRockMandateContinuity2008_2020 : Lane3
  blackRockNineBankExposureVerification : Lane3
  priorSystemicFront : Lane3

record Profile3 : Set where
  constructor profile3
  field
    lane : Lane3
    priority : Nat
    directEvidenceHigh : Bool
    secondOrderLeverageHigh : Bool
    thirdOrderLeverageHigh : Bool
    sourceResolutionDebtHigh : Bool
    reading : String
open Profile3 public

canonicalFront3 : List Profile3
canonicalFront3 =
  profile3 crisisDistributionalIncidence 100 true true true true
    "The bank-capital interventions and later homeowner programmes are both source-paid, so the live question is quantitative incidence: which security holders, institutions, households and public balance sheets received cash, loss protection or mark-to-market benefit, and on what timing/terms. 'Banks got help, homeowners got none' is false, but the asymmetry in scale/timing/reach is a legitimate measurement problem." ∷
  profile3 crisisStateFinancialAdvisoryInfrastructure 100 true true true true
    "Fink/BlackRock had deep mortgage-market expertise, crisis-period access to Paulson/Geithner/Fed officials and material Maiden Lane/advisory/implementation roles. This pays a private-expertise-to-state-capacity lane without making BlackRock the sovereign selector of TARP recipients or author of monetary policy." ∷
  profile3 blackRockMandateContinuity2008_2020 100 true true true true
    "BlackRock appears repeatedly in public crisis implementation: Bear/AIG/Maiden Lane in 2008 and the Fed corporate-credit facilities in 2020. The highest-value question is mandate/procurement/staff/model continuity and institutional learning, not a claim of identical authority across programmes." ∷
  profile3 blackRockNineBankExposureVerification 99 false true true true
    "The circulating claim that Fink/BlackRock was heavily invested in eight of the nine initial CPP institutions is not yet paid. Resolve manager-level holdings, client beneficial ownership and Fink personal ownership separately at announcement-date snapshots before promoting any bailout-beneficiary conflict claim." ∷
  profile3 priorSystemicFront 100 true true true true
    "Palantir state-capacity, banking/elite access, private-capital housing-AI-power assetisation, Wexner/Black/Apollo/Valar/Bear and Springfield incidence lanes remain co-frontier objects; the crisis-state lane cross-pollinates rather than replaces them."
  ∷ []

record Boundary3 : Set where
  constructor boundary3
  field
    adviserEqualsDecisionMaker : Bool
    managedAssetsEqualCEOPersonalAssets : Bool
    cmoEqualsCdo : Bool
    bailoutRecipientExposureEqualsSelectionCause : Bool
    implementationMandateEqualsPolicyAuthorship : Bool
    homeownerUnderperformanceEqualsNoHomeownerProgramme : Bool
    repeatedPublicMandatesEqualCapture : Bool
open Boundary3 public

canonicalBoundary3 : Boundary3
canonicalBoundary3 = boundary3 false false false false false false false

data AdviserImpliesDecisionMaker : Set where
data ManagedAssetsImpliesPersonalOwnership : Set where
data RepeatedMandateImpliesCapture : Set where

adviserDoesNotCreateDecisionAuthority : AdviserImpliesDecisionMaker → ⊥
adviserDoesNotCreateDecisionAuthority ()

managedAssetsDoNotCreatePersonalOwnership : ManagedAssetsImpliesPersonalOwnership → ⊥
managedAssetsDoNotCreatePersonalOwnership ()

repeatedMandateDoesNotCreateCapture : RepeatedMandateImpliesCapture → ⊥
repeatedMandateDoesNotCreateCapture ()

------------------------------------------------------------------------
-- Current max-cut.
------------------------------------------------------------------------

data Debt3 : Set where
  nineBankHoldingSnapshots : Debt3
  tarpAdviceDecisionChain : Debt3
  homeownerBankSupportCommonLedger : Debt3
  mandateContinuityAndFees : Debt3
  fed2020DesignExecutionSplit : Debt3
  crisisAssetHolderBeneficialOwnership : Debt3

record Acquisition3 : Set where
  constructor acquisition3
  field
    debt : Debt3
    priority : Nat
    instruction : String
open Acquisition3 public

canonicalAcquisition3 : List Acquisition3
canonicalAcquisition3 =
  acquisition3 nineBankHoldingSnapshots 100
    "Build announcement-date beneficial-ownership/manager-exposure snapshots for all nine initial CPP institutions; distinguish BlackRock-managed funds from Fink personal wealth and from Merrill/PNC ownership of BlackRock itself." ∷
  acquisition3 tarpAdviceDecisionChain 100
    "Reconstruct the primary decision chain for TARP/CPP from Paulson/Fed/FDIC records, then place each Fink/BlackRock call, memo or advisory object on that chain without converting access into decision authority." ∷
  acquisition3 homeownerBankSupportCommonLedger 100
    "Put CPP/AIG/asset-support cashflows and HAMP/HHF/homeowner assistance on one timing, obligation, disbursement, reach and loss-avoidance ledger." ∷
  acquisition3 mandateContinuityAndFees 99
    "Join 2008 Maiden Lane/Bear/AIG and 2020 CCF mandates by procurement route, scope, personnel, fees, conflicts controls, model/data ownership and subsequent selection advantage." ∷
  acquisition3 fed2020DesignExecutionSplit 99
    "Resolve BlackRock consultation in 2020 separately from the Fed/Treasury legal-policy design and the later investment-manager execution role." ∷
  acquisition3 crisisAssetHolderBeneficialOwnership 98
    "Measure second-order gains by security class and beneficial owner instead of treating all asset holders as one undifferentiated beneficiary."
  ∷ []
