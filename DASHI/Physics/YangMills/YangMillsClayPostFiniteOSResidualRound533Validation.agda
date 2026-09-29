{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPostFiniteOSResidualRound533Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayPostFiniteOSResidualRound533Exact as R533
open import DASHI.Physics.YangMills.CompactLieProofLevel

residualCountIsTwentySix :
  R533.residualLeafCount ≡ 26
residualCountIsTwentySix = refl

attachmentCountIsFive :
  R533.sourceLiteralAttachmentLeafCount ≡ 5
attachmentCountIsFive = refl

noEndpointSemantics :
  R533.opaqueEndpointSemanticLeavesRemaining ≡ false
noEndpointSemantics = refl
