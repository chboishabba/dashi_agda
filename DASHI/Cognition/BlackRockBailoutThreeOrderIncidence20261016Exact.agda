module DASHI.Cognition.BlackRockBailoutThreeOrderIncidence20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Cognition.SystemicLeverageBeneficiaryIncidenceParetoExact as Incidence
import DASHI.Governance.PalantirPlatformCapabilityEvidenceExact as Palantir

-- Treasury CPP 2008: USD 700bn TARP authorisation is not a disbursement.
-- Initial CPP authorisation USD 250bn, USD 125bn allocated to nine major
-- institutions, followed by wider participation. Treasury acquired preferred
-- stock and warrants. Sources: Treasury hp1207; GAO-09-522SP; Treasury CPP.
-- BlackRock advisory/management appointments require contract-specific
-- treatment distinct from public decision authority and private portfolio gains.

data BenefitOrder : Set where
  immediate : BenefitOrder
  marketReallocation : BenefitOrder
  institutionalPersistence : BenefitOrder

record IncidenceReceipt : Set where
  constructor incidence-receipt
  field
    beneficiary : String
    order : BenefitOrder
    mechanism : String
    paidObservation : Bool
    measuredNetBenefit : Bool
    causedPolicy : Bool
open IncidenceReceipt public

bankCapital : IncidenceReceipt
bankCapital = incidence-receipt "participating banks" immediate
  "preferred-equity capital injection and balance-sheet resilience" true false false

publicWarrantReturn : IncidenceReceipt
publicWarrantReturn = incidence-receipt "Treasury/taxpayers" immediate
  "preferred dividends, redemption and warrant proceeds; net public incidence separately measured" true false false

assetHolderRecovery : IncidenceReceipt
assetHolderRecovery = incidence-receipt "asset holders including financial intermediaries"
  marketReallocation
  "potential asset-price recovery and reduced fire-sale losses, conditional on exposure and counterfactual" false false false

assetManagerMandates : IncidenceReceipt
assetManagerMandates = incidence-receipt "contracted asset managers/advisers"
  marketReallocation
  "mandate fees, information and reputation advantages conditional on signed contracts" false false false

durableConcentration : IncidenceReceipt
durableConcentration = incidence-receipt "large financial institutions and incumbent managers"
  institutionalPersistence
  "possible concentration, procurement incumbency, market access and influence after crisis" false false false

householdForeclosure : IncidenceReceipt
householdForeclosure = incidence-receipt "mortgagors and tenants" institutionalPersistence
  "foreclosure, housing insecurity and unequal recovery burdens require household-level incidence" false false false

data Claim : Set where
  tarpAuthorised700 : Claim
  cppNineAllocated125 : Claim
  all700WentToNine : Claim
  finkSelectedNine : Claim
  blackrockOwnedEightOfNine : Claim
  finkInventedAllCDOs : Claim
  advisoryMandateEqualsDecisionPower : Claim
  institutionalAssetExposureEqualsFinkPersonalOwnership : Claim

claimPaid : Claim → Bool
claimPaid tarpAuthorised700 = true
claimPaid cppNineAllocated125 = true
claimPaid _ = false

data AdvisingImpliesSelecting : Set where
data ManagerExposureImpliesPersonalOwnership : Set where
data StabilisationImpliesEqualHouseholdRecovery : Set where
data BeneficiaryImpliesCrisisAuthorship : Set where

noAdvisingSelection : AdvisingImpliesSelecting → ⊥
noAdvisingSelection ()
noManagerPersonalOwnership : ManagerExposureImpliesPersonalOwnership → ⊥
noManagerPersonalOwnership ()
noEqualRecoveryInference : StabilisationImpliesEqualHouseholdRecovery → ⊥
noEqualRecoveryInference ()
noBeneficiaryAuthorshipInference : BeneficiaryImpliesCrisisAuthorship → ⊥
noBeneficiaryAuthorshipInference ()

record Acquisition : Set where
  constructor acquisition
  field
    priority : Nat
    object : String
    test : String
open Acquisition public

maxCut : List Acquisition
maxCut =
  acquisition 100 "BlackRock 2008 Fed/Treasury contract ledger"
    "Separate advice, asset management, fees, discretion, procurement decision and beneficiaries by contract" ∷
  acquisition 100 "2008 CPP nine-bank shareholder cross-section"
    "Reconstruct dated BlackRock-managed beneficial/13F exposures and Fink personal holdings; test eight-of-nine allegation" ∷
  acquisition 99 "2020 Fed corporate credit facility BlackRock mandate"
    "Join contract fees, conflicts, bond/ETF purchases and asset-holder incidence without inferring monetary-policy authorship" ∷
  acquisition 99 "foreclosure and recovery distribution"
    "Join household foreclosure outcomes, HAMP/HARP relief and asset-holder gains to public intervention dates" ∷
  acquisition 98 "first Boston structured-finance invention claim"
    "Distinguish Fink's early mortgage securitisation role from the invention of every CDO structure" ∷
  acquisition 98 "Palantir procurement and crisis-capital comparator"
    "Compare advisory-vendor incumbency and durable state capacity via existing typed incidence; no common-command inference" ∷ []
