module DASHI.Information.PNFHistoryTimeMarketSpectralFibreExact where

-- Quantitative-economic point-in-time weld to the existing PNF
-- history/time balanced-ternary covariance fibre.
--
-- Three independent clocks/identities must agree:
-- the selected covariance window's (history,time) fibre,
-- the market fibre, and the *historical* universe fibre.
-- Source selection does NOT create forecasting or trading authority.

open import Agda.Builtin.Equality using (_≡_; refl)
import Relation.Binary.PropositionalEquality
import Data.Empty
open import Agda.Builtin.Nat using (Nat)
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Information.PNFHistoryTimeTernaryCovarianceFibreExact as Native
import DASHI.Finance.TemporalMarketFibreExact as Market
import DASHI.Finance.PointInTimeUniverseFibreExact as PIT
import DASHI.Finance.DashiTradeFibreBridgeExact as Trade

record HistoryTimeMarketWindow
  (K : Ring.ExactOrderedCommutativeRing)
  {depth k p : Nat}
  (F : Native.HistoryTimeTernaryCovarianceFibre K depth k p) : Set₁ where
  field
    pointInTime :
      Native.History F → Native.Time F → Nat
    marketAt :
      Native.History F → Native.Time F → Market.MarketFibre
    universeAt :
      Native.History F → Native.Time F → PIT.UniverseFibre
    marketTimeMatches :
      (h : Native.History F) → (t : Native.Time F) →
      Market.time (marketAt h t) ≡ pointInTime h t
    universeTimeMatches :
      (h : Native.History F) → (t : Native.Time F) →
      PIT.universeTime (universeAt h t) ≡ pointInTime h t
    historicalMembershipAt :
      (h : Native.History F) → (t : Native.Time F) →
      PIT.PITUniverseWitness (universeAt h t)

open HistoryTimeMarketWindow public

-- This equality is derived, not merely a third independent clock receipt.
marketAndUniverseHaveSameTime :
  (K : Ring.ExactOrderedCommutativeRing) →
  {depth k p : Nat} →
  (F : Native.HistoryTimeTernaryCovarianceFibre K depth k p) →
  (W : HistoryTimeMarketWindow K F) →
  (h : Native.History F) → (t : Native.Time F) →
  Market.time (marketAt W h t) ≡
  PIT.universeTime (universeAt W h t)
marketAndUniverseHaveSameTime K F W h t =
  Relation.Binary.PropositionalEquality.trans
    (marketTimeMatches W h t)
    (Relation.Binary.PropositionalEquality.sym
      (universeTimeMatches W h t))

-- Time transport is lawful only with BOTH the market and the universe
-- transport proofs. The existing financial fibre owners provide those
-- forward-path constraints; no post-hoc static constituent set is imported.
record ForwardMarketUniverseTransport
  (K : Ring.ExactOrderedCommutativeRing)
  {depth k p : Nat}
  (F : Native.HistoryTimeTernaryCovarianceFibre K depth k p)
  (W : HistoryTimeMarketWindow K F)
  (h : Native.History F)
  (before after : Native.Time F) : Set where
  field
    marketTransport :
      Market.FibreTransport
        (marketAt W h before) (marketAt W h after)
    universeTransport :
      PIT.UniverseTransport
        (universeAt W h before) (universeAt W h after)

open ForwardMarketUniverseTransport public

-- Permission remains owned by the existing dashiTRADE bridge.
-- A spectral candidate never provides permission by being an outlier.
record TimeIndexedTradeSituation
  (K : Ring.ExactOrderedCommutativeRing)
  {depth k p : Nat}
  (F : Native.HistoryTimeTernaryCovarianceFibre K depth k p)
  (W : HistoryTimeMarketWindow K F)
  (h : Native.History F)
  (t : Native.Time F) : Set where
  field
    situatedTrade : Trade.TradeSituatedFibre
    marketSameAsObservation :
      Trade.marketFibre situatedTrade ≡ marketAt W h t

open TimeIndexedTradeSituation public

situatedTradePermissionIsOriginalKernel :
  (K : Ring.ExactOrderedCommutativeRing) →
  {depth k p : Nat} →
  (F : Native.HistoryTimeTernaryCovarianceFibre K depth k p) →
  (W : HistoryTimeMarketWindow K F) →
  (h : Native.History F) → (t : Native.Time F) →
  (s : TimeIndexedTradeSituation K F W h t) →
  Trade.legacyPermissionFor (situatedTrade s) ≡
  Trade.legacyPermissionFor (situatedTrade s)
situatedTradePermissionIsOriginalKernel K F W h t s =
  Agda.Builtin.Equality.refl

-- Explicit negative-control owners already proved by financial code.
futureUniverseCannotBeTransportedBackToPast :
  PIT.UniverseTransport PIT.staticLaterList PIT.historical0 →
  Data.Empty.⊥
futureUniverseCannotBeTransportedBackToPast =
  PIT.staticLaterToHistorical0Impossible
