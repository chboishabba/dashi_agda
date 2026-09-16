module DASHI.Finance.TrumpFamilyTradeSituatedActionabilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas
import DASHI.Finance.TrumpFamilyTradeSourceAtlas2026SupplementExact as Supplement
import DASHI.Finance.DashiTradeFibreBridgeExact as Trade
import DASHI.Trading.DashiTradeDreamOptionConeExact as Dream

------------------------------------------------------------------------
-- SOURCE-BACKED EVENT x SITUATED DASHITRADE FIBRE
--
-- A documentary transaction event is a world/evidence coordinate, not a trade
-- instruction. The same exact evidence claim may be considered in different
-- market/portfolio/execution fibres, and actionability can differ.
------------------------------------------------------------------------

record SourceBackedTradeContext : Set₁ where
  constructor source-backed-trade-context
  field
    evidenceClaim : Atlas.TradeEvidenceClaim
    situatedFibre : Trade.TradeSituatedFibre
    sourceClaimPaid : Atlas.primarySourcePaid evidenceClaim ≡ true

open SourceBackedTradeContext public

nvidiaSaleCleanContext : SourceBackedTradeContext
nvidiaSaleCleanContext =
  source-backed-trade-context
    Supplement.trumpOGE278TNvidiaSale
    Trade.cleanLongTradeFibre
    refl

nvidiaSaleCrowdedContext : SourceBackedTradeContext
nvidiaSaleCrowdedContext =
  source-backed-trade-context
    Supplement.trumpOGE278TNvidiaSale
    Trade.crowdedLongTradeFibre
    refl

sameEvidenceAcrossSituatedFibres :
  evidenceClaim nvidiaSaleCleanContext
  ≡ evidenceClaim nvidiaSaleCrowdedContext
sameEvidenceAcrossSituatedFibres = refl

sameDocumentaryEvidenceDifferentBuyActionability :
  Dream.actionAvailable
      (Trade.tradeFabric (situatedFibre nvidiaSaleCleanContext))
      Dream.buyAction
  ≡
  Dream.actionAvailable
      (Trade.tradeFabric (situatedFibre nvidiaSaleCrowdedContext))
      Dream.buyAction
  → ⊥
sameDocumentaryEvidenceDifferentBuyActionability =
  Trade.buyAvailabilityDiffersAcrossTradeFibres

amazonSaleCleanContext : SourceBackedTradeContext
amazonSaleCleanContext =
  source-backed-trade-context
    Supplement.trumpOGE278TAmazonMarchSale
    Trade.cleanLongTradeFibre
    refl

sameSituatedFibreDoesNotCollapseTransactionIdentity :
  Atlas.claimId (evidenceClaim nvidiaSaleCleanContext)
  ≡ Atlas.claimId (evidenceClaim amazonSaleCleanContext) → ⊥
sameSituatedFibreDoesNotCollapseTransactionIdentity ()

record TrumpFamilyTradeSituatedActionabilityBoundary : Set where
  constructor trump-family-trade-situated-actionability-boundary
  field
    sourceEvidenceAndTradeStateAreOrthogonalCoordinates : Bool
    sameEvidenceCanHaveDifferentActionability : Bool
    sameTradeStateDoesNotCollapseDistinctTransactions : Bool
    filingPresenceDoesNotCreateAuthorization : Bool
    historicalActorTradeDoesNotBecomeRecommendation : Bool

canonicalTrumpFamilyTradeSituatedActionabilityBoundary :
  TrumpFamilyTradeSituatedActionabilityBoundary
canonicalTrumpFamilyTradeSituatedActionabilityBoundary =
  trump-family-trade-situated-actionability-boundary true true true true true
