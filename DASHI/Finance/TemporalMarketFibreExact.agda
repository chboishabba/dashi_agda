module DASHI.Finance.TemporalMarketFibreExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.CausalRegimeMeasureFrame as Regime

------------------------------------------------------------------------
-- Markets are fibres over time, not a flat time series.
--
-- A fibre carries the state visible/available at one time together with
-- provenance and authority metadata.  Transport is deliberately forward and
-- receipt-bearing.  No transport creates forecasting/pricing authority.
------------------------------------------------------------------------

record MarketFibre : Set where
  constructor marketFibre
  field
    time : Nat
    universeSnapshot : String
    observationSurface : String
    factorState : String
    residualState : String
    executionState : String
    provenance : String
    authority : String

open MarketFibre public

data ForwardStep : Nat → Nat → Set where
  stay : {t : Nat} → ForwardStep t t
  next : {t : Nat} → ForwardStep t (suc t)

data ForwardPath : Nat → Nat → Set where
  path-id : {t : Nat} → ForwardPath t t
  path-next : {s t : Nat} → ForwardPath s t → ForwardPath s (suc t)

record FibreTransport (source target : MarketFibre) : Set where
  constructor fibreTransport
  field
    temporalPath : ForwardPath (time source) (time target)
    sourceProvenancePreserved : Bool
    sourceProvenancePreservedIsTrue : sourceProvenancePreserved ≡ true
    transportCreatesAuthority : Bool
    transportCreatesAuthorityIsFalse : transportCreatesAuthority ≡ false

open FibreTransport public

record MarketEvaluation : Set where
  constructor marketEvaluation
  field
    fibre : MarketFibre
    frame : Regime.EvaluationFrame
    statement : String

open MarketEvaluation public

forecastingEvaluation : MarketFibre → String → MarketEvaluation
forecastingEvaluation f s =
  marketEvaluation f Regime.forecastFrame s

pricingEvaluation : MarketFibre → String → MarketEvaluation
pricingEvaluation f s =
  marketEvaluation f Regime.pricingFrame s

record FibreAuthorityBoundary : Set where
  constructor fibreAuthorityBoundary
  field
    sameProjectionImpliesSameAuthority : Bool
    sameProjectionImpliesSameAuthorityIsFalse :
      sameProjectionImpliesSameAuthority ≡ false
    transportImpliesPromotion : Bool
    transportImpliesPromotionIsFalse : transportImpliesPromotion ≡ false

canonicalFibreAuthorityBoundary : FibreAuthorityBoundary
canonicalFibreAuthorityBoundary =
  fibreAuthorityBoundary false refl false refl

------------------------------------------------------------------------
-- Canonical one-step example and explicit reverse-transport impossibility.
------------------------------------------------------------------------

fibre0 : MarketFibre
fibre0 =
  marketFibre 0
    "historical-universe@0"
    "observations@0"
    "factor-state@0"
    "residual-state@0"
    "execution-state@0"
    "point-in-time provenance@0"
    "candidate-only"

fibre1 : MarketFibre
fibre1 =
  marketFibre 1
    "historical-universe@1"
    "observations@1"
    "factor-state@1"
    "residual-state@1"
    "execution-state@1"
    "point-in-time provenance@1"
    "candidate-only"

forward01 : FibreTransport fibre0 fibre1
forward01 =
  fibreTransport
    (path-next path-id)
    true refl
    false refl

noBackwardPath10 : ForwardPath 1 0 → ⊥
noBackwardPath10 ()

noBackwardTransport10 : FibreTransport fibre1 fibre0 → ⊥
noBackwardTransport10 tr = noBackwardPath10 (temporalPath tr)
