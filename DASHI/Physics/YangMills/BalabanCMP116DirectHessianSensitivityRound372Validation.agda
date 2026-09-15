module DASHI.Physics.YangMills.BalabanCMP116DirectHessianSensitivityRound372Validation where

import DASHI.Physics.YangMills.BalabanCMP116DirectHessianSensitivityRound372Exact as R372

open R372 public using
  ( CMP116DirectHessianSensitivityData
  ; sourceHessianLipschitz
  ; sourceHessianStableFromCauchy
  ; round372ToR352Source
  ; hLocalPrimitiveAfterRound372
  ; hLocalPrimitiveAfterRound372IsFalse
  ; separateThirdDerivativeTheoremMandatoryAfterRound372
  ; separateThirdDerivativeTheoremMandatoryAfterRound372IsFalse
  ; fullPhysicalSubstitutionChainRuleMandatoryForR352
  ; fullPhysicalSubstitutionChainRuleMandatoryForR352IsFalse
  ; canonicalRound372Boundary
  ; clayPromotion
  ; clayPromotionIsFalse
  )
