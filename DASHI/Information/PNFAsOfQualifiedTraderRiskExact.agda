module DASHI.Information.PNFAsOfQualifiedTraderRiskExact where

-- Consumer-side as-of certification of a measured finite held-out risk
-- ledger. No hindsight fold, later membership or changed consumer
-- version may qualify a present-time risk estimate.
--
-- A qualification is NOT permission, prediction, alpha or a cost
-- minimisation theorem. Existing permission/control owners are reused.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (_≤_)

import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Information.PNFHistoryTimeTernaryCovarianceFibreExact as Native
import DASHI.Information.PNFHistoryTimeMarketSpectralFibreExact as Market
import DASHI.Information.PNFTimeIndexedRiskQualityLedgerExact as Ledger
import DASHI.Information.PNFMPTradingInadequacyControlExact as Adequacy
import DASHI.Trading.PermissionKernel as Legacy
import DASHI.Finance.DashiTradeFibreBridgeExact as Trade
import DASHI.Finance.PointInTimeUniverseFibreExact as PIT
import DASHI.Finance.TradingPermissionActionRefinementExact as Refined

record AsOfQualifiedTraderRisk
  (K : Ring.ExactOrderedCommutativeRing)
  {depth k p m : Nat}
  (F : Native.HistoryTimeTernaryCovarianceFibre K depth k p)
  (W : Market.HistoryTimeMarketWindow K F)
  (h : Native.History F)
  (t : Native.Time F) : Set₁ where
  field
    selectedTrade : Market.TimeIndexedTradeSituation K F W h t
    ledger : Ledger.PointInTimeLossLedger m
    quality : Ledger.QualifiedRiskEvidence ledger
    encodeConsumerVersion : Nat → String
    historyReference : Native.History F → String

    sourceMatched :
      Ledger.sourceReference ledger ≡ Native.sourceReferenceAt F h t
    historyMatched :
      Ledger.historyReference ledger ≡ historyReference h
    consumerVersionMatched :
      Ledger.consumerVersionReference ledger
      ≡ encodeConsumerVersion (Native.consumerVersionAt F h t)
    historicalUniverseMatched :
      Ledger.featureUniverseReference ledger
      ≡ PIT.constituentSet (Market.universeAt W h t)

    -- Held-out scoring information was actually available at the
    -- current observation/decision point. Training-only causal
    -- correctness is not enough to prevent hindsight qualification.
    allEvaluationsAvailableAsOf :
      (i : Fin m) →
      Ledger.observationAvailableAt ledger i
        ≤ Market.pointInTime W h t

open AsOfQualifiedTraderRisk public

asOfRiskQualificationDelegatesToOriginalPermission :
  (K : Ring.ExactOrderedCommutativeRing) →
  {depth k p m : Nat} →
  (F : Native.HistoryTimeTernaryCovarianceFibre K depth k p) →
  (W : Market.HistoryTimeMarketWindow K F) →
  (h : Native.History F) → (t : Native.Time F) →
  (Q : AsOfQualifiedTraderRisk K {m = m} F W h t) →
  Legacy.Permission
asOfRiskQualificationDelegatesToOriginalPermission K F W h t Q =
  Adequacy.guardedPermission
    (Ledger.qualityReceiptEnablesSelectedRiskStatus
      (ledger Q) (quality Q))
    (Trade.legacyWindow (Market.situatedTrade (selectedTrade Q)))

qualifiedHeldoutCannotCreatePermission :
  (K : Ring.ExactOrderedCommutativeRing) →
  {depth k p m : Nat} →
  (F : Native.HistoryTimeTernaryCovarianceFibre K depth k p) →
  (W : Market.HistoryTimeMarketWindow K F) →
  (h : Native.History F) → (t : Native.Time F) →
  (Q : AsOfQualifiedTraderRisk K {m = m} F W h t) →
  asOfRiskQualificationDelegatesToOriginalPermission K F W h t Q
  ≡ Trade.legacyPermissionFor (Market.situatedTrade (selectedTrade Q))
qualifiedHeldoutCannotCreatePermission K F W h t Q = refl

asOfRiskStillUsesExposureAwareControl :
  (K : Ring.ExactOrderedCommutativeRing) →
  {depth k p m : Nat} →
  (F : Native.HistoryTimeTernaryCovarianceFibre K depth k p) →
  (W : Market.HistoryTimeMarketWindow K F) →
  (h : Native.History F) → (t : Native.Time F) →
  (Q : AsOfQualifiedTraderRisk K {m = m} F W h t) →
  Refined.ExposureState → Refined.ExecutionIntent
asOfRiskStillUsesExposureAwareControl K F W h t Q exposure =
  Refined.compileIntent
    (asOfRiskQualificationDelegatesToOriginalPermission K F W h t Q)
    exposure
