module DASHI.Information.PNFMPTradingInadequacyControlExact where

-- The reel's MP sample-noise warning is a covariance-estimation ADEQUACY
-- issue. It is not an alpha signal or trading permission.
-- This adapter reuses the actual legacy permission state machine and
-- the richer trading option cone / exposure-action refinement.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Trading.PermissionKernel as Legacy
import DASHI.Trading.DashiTradeDreamOptionConeExact as Dream
import DASHI.Finance.TradingPermissionActionRefinementExact as Refined

-- Distinguish statistically uncalibrated risk estimation from an
-- ordinary MP bulk-only finding. The latter is NOT a prohibition.
data SpectralAdequacy : Set where
  inadequateSample : SpectralAdequacy
  uncalibratedNull : SpectralAdequacy
  qualifiedRiskEstimate : SpectralAdequacy
  bulkOnlyQualified : SpectralAdequacy
  outlierCandidateQualified : SpectralAdequacy

-- This is an explicitly chosen conservative policy for inadequate risk
-- information. It never clears an existing risk BLOCKED status.
riskUnderSpectralAdequacy :
  SpectralAdequacy → Legacy.RiskGate → Legacy.RiskGate
riskUnderSpectralAdequacy inadequateSample Legacy.clear = Legacy.caution
riskUnderSpectralAdequacy inadequateSample Legacy.caution = Legacy.caution
riskUnderSpectralAdequacy inadequateSample Legacy.blocked = Legacy.blocked
riskUnderSpectralAdequacy uncalibratedNull Legacy.clear = Legacy.caution
riskUnderSpectralAdequacy uncalibratedNull Legacy.caution = Legacy.caution
riskUnderSpectralAdequacy uncalibratedNull Legacy.blocked = Legacy.blocked
riskUnderSpectralAdequacy qualifiedRiskEstimate r = r
riskUnderSpectralAdequacy bulkOnlyQualified r = r
riskUnderSpectralAdequacy outlierCandidateQualified r = r

-- Preserve actual feature state and all cost coordinates. Re-run the
-- original kernel on the changed *risk* gate. Do not rewrite a prior
-- permission and do not reinterpret ACT/HOLD/BAN as buy/sell direction.
guardedMarketState :
  SpectralAdequacy →
  Legacy.MarketWindowState → Legacy.MarketWindowState
guardedMarketState q s =
  Legacy.marketState
    (Legacy.shape s)
    (Legacy.energy s)
    (Legacy.persistence s)
    (Legacy.liquidity s)
    (riskUnderSpectralAdequacy q (Legacy.risk s))
    (Legacy.modelCost s)
    (Legacy.residualCost s)
    (Legacy.riskPenalty s)
    (Legacy.currentPermission s)

guardedPermission :
  SpectralAdequacy → Legacy.MarketWindowState → Legacy.Permission
guardedPermission q s =
  Legacy.authorize (Legacy.quotient (guardedMarketState q s))

-- The adapter genuinely delegates to the original permission kernel.
guardedPermissionIsOriginalKernel :
  (q : SpectralAdequacy) → (s : Legacy.MarketWindowState) →
  Legacy.currentPermission
    (Legacy.permissionKernel (guardedMarketState q s))
  ≡ guardedPermission q s
guardedPermissionIsOriginalKernel q s = refl

-- Adequacy is explicitly a no-lookahead risk-policy input; it cannot
-- manufacture a favourable risk gate by reclassifying an MP eigenvalue.
riskBlockedRemainsBlocked :
  (q : SpectralAdequacy) →
  riskUnderSpectralAdequacy q Legacy.blocked ≡ Legacy.blocked
riskBlockedRemainsBlocked inadequateSample = refl
riskBlockedRemainsBlocked uncalibratedNull = refl
riskBlockedRemainsBlocked qualifiedRiskEstimate = refl
riskBlockedRemainsBlocked bulkOnlyQualified = refl
riskBlockedRemainsBlocked outlierCandidateQualified = refl

bulkOnlyDoesNotForceRiskWarning :
  (r : Legacy.RiskGate) →
  riskUnderSpectralAdequacy bulkOnlyQualified r ≡ r
bulkOnlyDoesNotForceRiskWarning r = refl

outlierDoesNotForceRiskClear :
  (r : Legacy.RiskGate) →
  riskUnderSpectralAdequacy outlierCandidateQualified r ≡ r
outlierDoesNotForceRiskClear r = refl

-- Concrete original state-machine regression.
canonicalClear :
  Legacy.MarketWindowState
canonicalClear =
  Legacy.marketState
    Legacy.upward Legacy.calm Legacy.persistent Legacy.adequate
    Legacy.clear 0 0 0 Legacy.HOLD

clearPreviouslyActs :
  guardedPermission qualifiedRiskEstimate canonicalClear ≡ Legacy.ACT
clearPreviouslyActs = refl

inadequateSampleWithdrawsNewRiskPermission :
  guardedPermission inadequateSample canonicalClear ≡ Legacy.HOLD
inadequateSampleWithdrawsNewRiskPermission = refl

uncalibratedNullWithdrawsNewRiskPermission :
  guardedPermission uncalibratedNull canonicalClear ≡ Legacy.HOLD
uncalibratedNullWithdrawsNewRiskPermission = refl

bulkOnlyDoesNotBlockAnOtherwisePermittedState :
  guardedPermission bulkOnlyQualified canonicalClear ≡ Legacy.ACT
bulkOnlyDoesNotBlockAnOtherwisePermittedState = refl

-- Crucially BAN is not "freeze the book". The existing refined
-- controller may still reduce exposure in the face of inadequate risk.
inadequateBlockedLongCanReduce :
  Refined.compileIntent Legacy.BAN Refined.longExposure
  ≡ Refined.reduceExposure
inadequateBlockedLongCanReduce =
  Refined.banLongCompilesToActLikeReduction

-- A single spectral adequacy label cannot reconstruct action
-- availability, even if every label were "qualified".
qualifiedSpectrumOfState : Dream.TradingFabricState → SpectralAdequacy
qualifiedSpectrumOfState _ = qualifiedRiskEstimate

sameQualifiedSpectrumDifferentBuyAvailability :
  NF.NonFactorabilityWitness
    qualifiedSpectrumOfState
    (λ s → Dream.actionAvailable s Dream.buyAction)
sameQualifiedSpectrumDifferentBuyAvailability =
  NF.nonFactorabilityWitness
    Dream.cleanLongState
    Dream.crowdedLongState
    refl
    Dream.buyAvailabilityDiffers

noSpectralAdequacyOnlyBuyCompiler :
  NF.FactorsThrough qualifiedSpectrumOfState
    (λ s → Dream.actionAvailable s Dream.buyAction) →
  ⊥
noSpectralAdequacyOnlyBuyCompiler =
  NF.witnessRulesOutEveryFlatFactorisation
    sameQualifiedSpectrumDifferentBuyAvailability
