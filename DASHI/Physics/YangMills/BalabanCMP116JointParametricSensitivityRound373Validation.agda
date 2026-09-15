module DASHI.Physics.YangMills.BalabanCMP116JointParametricSensitivityRound373Validation where

import DASHI.Physics.YangMills.BalabanCMP116JointParametricSensitivityRound373Exact as R373

open R373 public using
  ( JointBoundaryHessianPaymentData
  ; boundaryNormDifference
  ; boundaryHessianStableFromR372
  ; hLocalOpaquePrimitiveAfterRound373
  ; hLocalOpaquePrimitiveAfterRound373IsFalse
  ; sameObjectScalarizationStillRequiredAfterRound373
  ; sameObjectScalarizationStillRequiredAfterRound373IsTrue
  ; canonicalRound373Boundary
  ; clayPromotion
  ; clayPromotionIsFalse
  )
