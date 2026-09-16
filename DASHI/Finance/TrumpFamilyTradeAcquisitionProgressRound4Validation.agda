module DASHI.Finance.TrumpFamilyTradeAcquisitionProgressRound4Validation where

import DASHI.Finance.TrumpFamilyTradePrimarySourceRound2Exact as Primary2
import DASHI.Finance.TrumpFamilyTradeSourceQualityRound4Exact as Quality4
import DASHI.Finance.TrumpFamilyTradeAcquisitionProgressRound4Exact as Progress4
import DASHI.Finance.TrumpFamilyPolicyMarketSourceAtlasExact as Policy
import DASHI.Finance.TrumpFamilyPolicyMarketPNFBridgeExact as PolicyPNF

------------------------------------------------------------------------
-- Regression surface for the canonical post-acquisition state.
------------------------------------------------------------------------

ericTrustTransfer = Primary2.ericAmericanBitcoinTrustTransfer
ericCashPurchase = Primary2.ericAmericanBitcoinCashPurchase
ericCashPurchaseCorroboration = Quality4.ericCashPurchaseCorroborationPair

round4Progress = Progress4.currentTrumpFamilyTradeAcquisitionProgressRound4

grabAGunTriad = Policy.canonicalGrabAGunPolicyMarketTriad
truthAPIMarketTriad = Policy.canonicalTruthAPIPolicyMarketTriad
policyMarketPNFBoundary = PolicyPNF.canonicalPolicyMarketPNFBoundary
