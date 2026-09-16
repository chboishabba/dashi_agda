module DASHI.Finance.TrumpFamilyTradeAcquisitionParetoValidation where

import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas
import DASHI.Finance.TrumpFamilyTradeAcquisitionParetoExact as Pareto

------------------------------------------------------------------------
-- RED regression surface.
--
-- The source atlas must retain exact primary-source witnesses for the next
-- acquisition tranche, and the acquisition owner must expose a consumer-safe
-- source-debt frontier rather than another generic scheduler.
------------------------------------------------------------------------

ericABTCInitial13DIsPresent = Atlas.ericAmericanBitcoinInitial13D
ericABTCTrustTransferIsPresent = Atlas.ericAmericanBitcoinTrustTransfer
ericABTCCashPurchaseIsPresent = Atlas.ericAmericanBitcoinCashPurchase

donJrPSQHPaidPurchaseIsPresent = Atlas.donJrPSQHPaidPurchase2026Aug13

acquisitionFrontierIsPresent = Pareto.canonicalTrumpFamilyTradeAcquisitionFrontier
primaryDeficitCannotBePaidBySecondaryOnly = Pareto.secondaryOnlyCannotPayPrimaryDebt
