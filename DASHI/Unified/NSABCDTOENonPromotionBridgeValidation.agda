module DASHI.Unified.NSABCDTOENonPromotionBridgeValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSABCDMaxCut20261002Exact as MaxCut
import DASHI.Unified.NSABCDTOENonPromotionBridgeExact as Bridge

aFrontierRegression :
  MaxCut.aIrreducibleLeafCount ≡ 3
aFrontierRegression =
  Bridge.aMaxCutHasThreeIrreducibleLeaves

bDecisionRegression :
  MaxCut.bDecisionExternalLeafCount ≡ 2
bDecisionRegression =
  Bridge.bDecisionHasTwoExternalLeaves

bRealODERegression :
  MaxCut.bRealODEInternalBridgeLeafCount ≡ 2
bRealODERegression =
  Bridge.bRealODEHasTwoInternalBridgeLeaves

r823ReserveRegression :
  MaxCut.r823AdditionalReserveEstimateNeededAfterDecisionLeaves ≡ false
r823ReserveRegression =
  Bridge.r823NeedsNoAdditionalReserveEstimateAfterDecisionLeaves

helicalGateRegression :
  MaxCut.globalRationalHelicalProjectorLawsGateR829Decision ≡ false
helicalGateRegression =
  Bridge.globalRationalHelicalProjectorLawsDoNotGateR829Decision

cAuditRegression :
  MaxCut.cOfficialSourceAuditClosed ≡ true
cAuditRegression =
  Bridge.cOfficialSourceAuditIsClosed

dAuditRegression :
  MaxCut.dOfficialSourceAuditClosed ≡ true
dAuditRegression =
  Bridge.dOfficialSourceAuditIsClosed

clayNonPromotionRegression :
  MaxCut.clayPromotion ≡ false
clayNonPromotionRegression =
  Bridge.nsClayPromotionRemainsFalse

canonicalReceiptRegression :
  Bridge.NSABCDTOEConvergenceReceipt
canonicalReceiptRegression =
  Bridge.canonicalNSABCDTOEConvergenceReceipt
