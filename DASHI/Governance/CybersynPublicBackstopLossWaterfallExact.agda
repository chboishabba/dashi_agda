module DASHI.Governance.CybersynPublicBackstopLossWaterfallExact where

-- DASHI original: finite public/private loss-waterfall algebra.
-- Illustrative amounts are not observed company or government exposures.
-- Attribution: Docs/SourceAttributionPolicy.md.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Economics.PolicyBackstopCommercialDisciplineExact as Policy
import DASHI.Governance.CybersynGlobalViabilityMaxCutExact as Cyber
import DASHI.Governance.CybersynCrossSectorScenarioExact as Scenario
import DASHI.Planning.MultiAxisAuthorityFabricExact as Axis
import DASHI.Governance.NonCompensatoryJusticeOrderExact as Justice
import DASHI.Core.IntersectionalNonFactorability as NonFactor

-- Conservation is constructed explicitly, not guessed from reported profits.
-- All figures here are natural-valued accounting units.
record LossWaterfall : Set where
  constructor lossWaterfall
  field
    equityLoss : Nat
    lenderLoss : Nat
    publicLoss : Nat
    totalLoss : Nat
    balances : totalLoss ≡ equityLoss + (lenderLoss + publicLoss)

open LossWaterfall public

allocateLoss : (equity lender publicShare : Nat) → LossWaterfall
allocateLoss equity lender publicShare =
  lossWaterfall equity lender publicShare
    (equity + (lender + publicShare)) refl

privateAbsorption : LossWaterfall
privateAbsorption = allocateLoss 4 3 0

publicBackstop : LossWaterfall
publicBackstop = allocateLoss 2 1 4

sameTotalLoss :
  totalLoss privateAbsorption ≡ totalLoss publicBackstop
sameTotalLoss = refl

data InvestorHeadline : Set where
  infrastructureInvestmentContinues : InvestorHeadline

report : LossWaterfall → InvestorHeadline
report _ = infrastructureInvestmentContinues

publicExposure : LossWaterfall → Nat
publicExposure = publicLoss

sameReportedInvestment :
  report privateAbsorption ≡ report publicBackstop
sameReportedInvestment = refl

differentPublicExposure :
  publicExposure privateAbsorption ≡
  publicExposure publicBackstop → ⊥
differentPublicExposure ()

-- Aggregate loss and identical investment publicity do not recover which
-- actor carries the actual loss.  Use the repository's constructive
-- intersectional non-factorability criterion, rather than a generic slogan.
data WaterfallCase : Set where
  privateCase : WaterfallCase
  publicCase : WaterfallCase

waterfallFor : WaterfallCase → LossWaterfall
waterfallFor privateCase = privateAbsorption
waterfallFor publicCase = publicBackstop

aggregateLoss : WaterfallCase → Nat
aggregateLoss caseName = totalLoss (waterfallFor caseName)

publicBurden : WaterfallCase → Nat
publicBurden caseName = publicLoss (waterfallFor caseName)

sameAggregateLoss :
  aggregateLoss privateCase ≡ aggregateLoss publicCase
sameAggregateLoss = refl

differentTaxpayerBurden :
  publicBurden privateCase ≡ publicBurden publicCase → ⊥
differentTaxpayerBurden ()

aggregateLossCannotRecoverTaxpayerBurden :
  NonFactor.FactorsThrough aggregateLoss publicBurden → ⊥
aggregateLossCannotRecoverTaxpayerBurden =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      privateCase publicCase
      sameAggregateLoss differentTaxpayerBurden)

investmentHeadlineCannotRecoverTaxpayerBurden :
  NonFactor.FactorsThrough
    (λ caseName → report (waterfallFor caseName))
    publicBurden → ⊥
investmentHeadlineCannotRecoverTaxpayerBurden =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      privateCase publicCase
      sameReportedInvestment differentTaxpayerBurden)

-- A public backstop changes distribution despite identical aggregate loss.
-- It cannot generate commercial viability, actual permission or justice.
policySupportNotProofOfReturn :
  Policy.PolicySupportImpliesCommercialViabilityPermission → ⊥
policySupportNotProofOfReturn =
  Policy.policySupportDoesNotAutoPromoteToCommercialViability

strategyNotNPV :
  Policy.StrategicValueImpliesPositiveNPVPermission → ⊥
strategyNotNPV = Policy.strategicValueDoesNotAutoPromoteToPositiveNPV

authorityByAxis : Axis.AuthorityFabricBoundary
authorityByAxis = Axis.canonicalAuthorityFabricBoundary

justiceNeedsNonCompensation : Justice.CompensationPolicy
justiceNeedsNonCompensation = Justice.sameInvariantCompensationPolicy

-- Gross investment announcements can be equal with different social
-- liabilities; record the statutory, fiscal and equity surfaces separately.
record PublicGuaranteeAdmission : Set where
  constructor guaranteeAdmission
  field
    fiscalExposureDisclosed : Bool
    liabilityLegallyAuthorised : Bool
    communityDecisionAuthority : Bool
    ecologicalConstraintsMet : Bool
    bankSolvencyStressTested : Bool
    insurerSolvencyStressTested : Bool

open PublicGuaranteeAdmission public

infixr 6 _and_
_and_ : Bool → Bool → Bool
true and b = b
false and _ = false

guaranteeAdmitted : PublicGuaranteeAdmission → Bool
guaranteeAdmitted g =
  fiscalExposureDisclosed g and
  liabilityLegallyAuthorised g and
  communityDecisionAuthority g and
  ecologicalConstraintsMet g and
  bankSolvencyStressTested g and
  insurerSolvencyStressTested g

-- Distinguish a rhetorical "no cost to consumers" claim from an actual
-- full-cost incidence receipt, which would need external measured evidence.
paperPromise : PublicGuaranteeAdmission
paperPromise = guaranteeAdmission true false false false false false

promiseNotCostRecovery :
  guaranteeAdmitted paperPromise ≡ false
promiseNotCostRecovery = refl

data GovernmentPressReleaseImpliesZeroPublicCost : Set where

noCostClaimDoesNotCancelPublicLiability :
  GovernmentPressReleaseImpliesZeroPublicCost → ⊥
noCostClaimDoesNotCancelPublicLiability ()
