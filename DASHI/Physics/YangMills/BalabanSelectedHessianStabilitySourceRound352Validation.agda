{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSelectedHessianStabilitySourceRound352Validation where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanSelectedHessianStabilitySourceRound352Exact as R352

literalCMP116LocalHessianStabilitySourceLevel : ProofLevel
literalCMP116LocalHessianStabilitySourceLevel =
  R352.literalCMP116LocalHessianStabilitySourceLevel

selectedR318R350HessianStabilityAttachmentLevel : ProofLevel
selectedR318R350HessianStabilityAttachmentLevel =
  R352.selectedR318R350HessianStabilityAttachmentLevel

selectedHessianStabilityTransportCompilerLevel : ProofLevel
selectedHessianStabilityTransportCompilerLevel =
  R352.selectedHessianStabilityTransportCompilerLevel

wilsonCoercivityDirectlyPaysHStab : Bool
wilsonCoercivityDirectlyPaysHStab = R352.wilsonCoercivityDirectlyPaysHStab

wilsonCoercivityDirectlyPaysHStabIsFalse :
  wilsonCoercivityDirectlyPaysHStab ≡ false
wilsonCoercivityDirectlyPaysHStabIsFalse =
  R352.wilsonCoercivityDirectlyPaysHStabIsFalse

clayPromotion : Bool
clayPromotion = R352.clayPromotion

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = R352.clayPromotionIsFalse
