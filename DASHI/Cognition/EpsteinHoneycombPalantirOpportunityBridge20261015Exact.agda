module DASHI.Cognition.EpsteinHoneycombPalantirOpportunityBridge20261015Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinSouthernTrustInvestmentFlowAtlas20261014Exact as Flow
import DASHI.Cognition.EpsteinPalantirInvestmentInterest20261015Exact as Palantir

------------------------------------------------------------------------
-- HONEYCOMB / FISZEL / PALANTIR OPPORTUNITY BRIDGE — 2026-10-15
--
-- Southern Trust was already a large Honeycomb investor before David Fiszel's
-- Palantir secondary-share opportunity was routed through Richard Kahn to
-- Epstein.  This pays counterparty continuity and opportunity routing.  It
-- does not identify the Palantir seller, investment vehicle, executed trade,
-- or prove that the opportunity was a Honeycomb fund/co-investment product.
------------------------------------------------------------------------

record CounterpartyBridge : Set where
  constructor counterparty-bridge
  field
    counterparty : String
    priorRelationship : String
    laterOpportunity : String
    priorCapitalRelationshipPaid : Bool
    laterOpportunityPaid : Bool
    sameCounterpartyPaid : Bool
    sameInvestmentVehiclePaid : Bool
    executionPaid : Bool
open CounterpartyBridge public

fiszelHoneycombPalantir : CounterpartyBridge
fiszelHoneycombPalantir = counterparty-bridge
  "David Fiszel / Honeycomb"
  "Southern Trust funded Honeycomb Partners with USD20m on 31 May 2016; later Honeycomb Ventures I received a USD1m Southern Trust co-investment wire in July 2017."
  "On 16 Dec 2016 Fiszel told Kahn he could buy more Palantir at USD5/share at an asserted USD9.5bn valuation; Kahn forwarded the opportunity to Epstein and described access as roughly a 50% market discount if Epstein's view was positive."
  true true true false false

record HoneycombPalantirBoundary : Set where
  constructor honeycomb-palantir-boundary
  field
    southernTrustHoneycombCapitalPaid : Bool
    fiszelPalantirAccessPaid : Bool
    kahnEpsteinRoutingPaid : Bool
    honeycombVehicleSoldPalantirShares : Bool
    southernTrustBoughtPalantirThroughHoneycomb : Bool
    sellerIdentityPaid : Bool
    shareCustodyPaid : Bool
open HoneycombPalantirBoundary public

canonicalHoneycombPalantirBoundary : HoneycombPalantirBoundary
canonicalHoneycombPalantirBoundary = honeycomb-palantir-boundary
  true true true false false false false

data SameManagerImpliesSameVehicle : Set where
data OpportunityImpliesHoneycombCoInvestment : Set where
data DiscountClaimImpliesFairMarketDiscount : Set where

sameManagerDoesNotCreateSameVehicle : SameManagerImpliesSameVehicle → ⊥
sameManagerDoesNotCreateSameVehicle ()

opportunityDoesNotCreateHoneycombCoInvestment : OpportunityImpliesHoneycombCoInvestment → ⊥
opportunityDoesNotCreateHoneycombCoInvestment ()

discountClaimDoesNotCreateFairMarketDiscount : DiscountClaimImpliesFairMarketDiscount → ⊥
discountClaimDoesNotCreateFairMarketDiscount ()

------------------------------------------------------------------------
-- Acquisition moves from relationship existence to transaction mechanics.
------------------------------------------------------------------------

data HoneycombPalantirDebt : Set where
  davidSellerPrincipalIdentity : HoneycombPalantirDebt
  shareSourceAndTransferAgent : HoneycombPalantirDebt
  tradeExecution : HoneycombPalantirDebt
  honeycombVehicleRelation : HoneycombPalantirDebt
  contemporaneousValuationComparator : HoneycombPalantirDebt
  laterPositionOrDisposition : HoneycombPalantirDebt

record HoneycombPalantirAcquisition : Set where
  constructor honeycomb-palantir-acquisition
  field
    debt : HoneycombPalantirDebt
    priority : Nat
    instruction : String
open HoneycombPalantirAcquisition public

canonicalHoneycombPalantirAcquisition : List HoneycombPalantirAcquisition
canonicalHoneycombPalantirAcquisition =
  honeycomb-palantir-acquisition davidSellerPrincipalIdentity 100
    "Resolve who supplied Fiszel's Palantir access, whether Fiszel acted personally, for Honeycomb, or for another vehicle, and identify the selling holder."
  ∷ honeycomb-palantir-acquisition shareSourceAndTransferAgent 100
    "Acquire term sheet, transfer-agent/cap-table, seller consent or secondary-platform records for the offered Palantir shares."
  ∷ honeycomb-palantir-acquisition tradeExecution 100
    "Search Southern Trust/HBRK/Honeycomb brokerage and wire records for execution or explicit rejection of the December 2016 opportunity."
  ∷ honeycomb-palantir-acquisition honeycombVehicleRelation 99
    "Determine whether the Palantir opportunity was a Honeycomb fund/co-investment product or a separate personal/network opportunity; same manager is insufficient."
  ∷ honeycomb-palantir-acquisition contemporaneousValuationComparator 98
    "Resolve the stated USD5/share / USD9.5bn valuation and '50% discount' against contemporaneous Palantir secondary trades without treating the sender's estimate as market fact."
  ∷ honeycomb-palantir-acquisition laterPositionOrDisposition 98
    "Only after execution is paid, trace later custody, transfer, sale or IPO conversion."
  ∷ []
