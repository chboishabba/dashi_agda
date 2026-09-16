module DASHI.Finance.TrumpFamilyTradeAcquisitionParetoValidation where

import DASHI.Finance.TrumpFamilyTradePrimarySourceRound2Exact as Primary2
import DASHI.Finance.TrumpFamilyTradeAcquisitionProgressRound4Exact as Progress4

------------------------------------------------------------------------
-- RED/GREEN regression: exact Eric-ABTC transaction mechanisms must live in the
-- canonical primary-source sequence, and acquisition progress must preserve the
-- still-unpaid independent/causal/knowledge coordinates.
------------------------------------------------------------------------

ericABTCTrustTransferIsPresent = Primary2.ericAmericanBitcoinTrustTransfer
ericABTCCashPurchaseIsPresent = Primary2.ericAmericanBitcoinCashPurchase

donJrPSQHPaidPurchaseIsPresent = Primary2.donJrPSQHPrivatePlacementPersonalAllocation

round4ProgressIsPresent = Progress4.currentTrumpFamilyTradeAcquisitionProgressRound4
cashPurchaseIndependentCorroborationIsPresent = Progress4.ericCashPurchaseIndependentCorroboration
