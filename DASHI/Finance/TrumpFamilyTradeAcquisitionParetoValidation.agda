module DASHI.Finance.TrumpFamilyTradeAcquisitionParetoValidation where

import DASHI.Finance.TrumpFamilyTradeSourceAtlasRound2Exact as Atlas2
import DASHI.Finance.TrumpFamilyTradeAcquisitionParetoExact as Pareto

------------------------------------------------------------------------
-- RED/GREEN regression surface.
------------------------------------------------------------------------

ericABTCInitial13DIsPresent = Atlas2.ericAmericanBitcoinInitial13D
ericABTCTrustTransferIsPresent = Atlas2.ericAmericanBitcoinTrustTransfer
ericABTCCashPurchaseIsPresent = Atlas2.ericAmericanBitcoinCashPurchase

donJrPSQHPaidPurchaseIsPresent = Atlas2.donJrPSQHPaidPurchase2026Aug13

acquisitionFrontierIsPresent = Pareto.canonicalTrumpFamilyTradeAcquisitionFrontier
primaryDeficitCannotBePaidBySecondaryOnly = Pareto.secondaryOnlyCannotPayPrimaryDebt
issuerMaterialCannotPayIndependenceDebt = Pareto.issuerMaterialCannotPayIndependentDebt
