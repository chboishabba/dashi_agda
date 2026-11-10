module DASHI.Information.PNFHistoryTimeTraderAdequacyExact where

-- The reel's finite-history spectral uncertainty is NOT a trading action.
-- Source-qualified, time-indexed risk estimation is a separate input to
-- the original permission kernel, after the historical universe is fixed.
-- The original inventory-aware exposure reducer remains authoritative.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Information.PNFHistoryTimeTernaryCovarianceFibreExact as Native
import DASHI.Information.PNFHistoryTimeMarketSpectralFibreExact as Market
import DASHI.Information.PNFMPTradingInadequacyControlExact as Adequacy
import DASHI.Finance.DashiTradeFibreBridgeExact as Trade
import DASHI.Trading.PermissionKernel as Legacy
import DASHI.Finance.TradingPermissionActionRefinementExact as Refined
import DASHI.Finance.PointInTimeUniverseFibreExact as PIT
import Data.Empty

-- The source-owned measurement window and historical market universe
-- are selected BEFORE a risk decision. This record does not manufacture
-- a market forecast from an MP diagnostic.
record TimeIndexedSpectralRiskAudit
  (K : Ring.ExactOrderedCommutativeRing)
  {depth k p : Nat}
  (F : Native.HistoryTimeTernaryCovarianceFibre K depth k p)
  (W : Market.HistoryTimeMarketWindow K F)
  (h : Native.History F)
  (t : Native.Time F) : Set where
  field
    tradeState : Market.TimeIndexedTradeSituation K F W h t
    riskAssessment : Adequacy.SpectralAdequacy
    sampleReceipt : String
    nullCalibrationReceipt : String
    outOfSampleRiskReceipt : String
    sourceVersion :
      Nat
    sourceVersionIsConsumerVersion :
      sourceVersion ≡ Native.consumerVersionAt F h t

open TimeIndexedSpectralRiskAudit public

-- The original legacy kernel is run *on the original situated state*
-- after the optional caution policy has been applied.
tradePermissionAfterSpectralAudit :
  (K : Ring.ExactOrderedCommutativeRing) →
  {depth k p : Nat} →
  (F : Native.HistoryTimeTernaryCovarianceFibre K depth k p) →
  (W : Market.HistoryTimeMarketWindow K F) →
  (h : Native.History F) → (t : Native.Time F) →
  TimeIndexedSpectralRiskAudit K F W h t → Legacy.Permission
tradePermissionAfterSpectralAudit K F W h t audit =
  Adequacy.guardedPermission (riskAssessment audit)
    (Trade.legacyWindow
      (Market.situatedTrade (tradeState audit)))

-- BAN is exposure-increase prohibition, not an unconditional refusal
-- to reduce risk on a pre-existing position.
tradeControlAfterSpectralAudit :
  (K : Ring.ExactOrderedCommutativeRing) →
  {depth k p : Nat} →
  (F : Native.HistoryTimeTernaryCovarianceFibre K depth k p) →
  (W : Market.HistoryTimeMarketWindow K F) →
  (h : Native.History F) → (t : Native.Time F) →
  (audit : TimeIndexedSpectralRiskAudit K F W h t) →
  Refined.ExposureState → Refined.ExecutionIntent
tradeControlAfterSpectralAudit K F W h t audit exposure =
  Refined.compileIntent
    (tradePermissionAfterSpectralAudit K F W h t audit)
    exposure

-- Inadequacy only changes the candidate risk gate. Whether a concrete
-- proposed action is permitted is *still* the existing refined kernel.
tradeControlAlwaysUsesOriginalCompiler :
  (K : Ring.ExactOrderedCommutativeRing) →
  {depth k p : Nat} →
  (F : Native.HistoryTimeTernaryCovarianceFibre K depth k p) →
  (W : Market.HistoryTimeMarketWindow K F) →
  (h : Native.History F) → (t : Native.Time F) →
  (audit : TimeIndexedSpectralRiskAudit K F W h t) →
  (exposure : Refined.ExposureState) →
  tradeControlAfterSpectralAudit K F W h t audit exposure
  ≡ Refined.compileIntent
    (tradePermissionAfterSpectralAudit K F W h t audit)
    exposure
tradeControlAlwaysUsesOriginalCompiler K F W h t audit exposure = refl

-- Historical universe cannot be sourced retroactively; reuse prior
-- Finance proof rather than introducing weaker temporal precedence.
noLaterUniverseBackdated :
  PIT.UniverseTransport
    PIT.staticLaterList
    PIT.historical0 →
  Data.Empty.⊥
noLaterUniverseBackdated =
  Market.futureUniverseCannotBeTransportedBackToPast
