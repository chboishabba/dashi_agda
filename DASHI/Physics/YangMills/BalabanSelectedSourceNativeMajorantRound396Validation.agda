{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSelectedSourceNativeMajorantRound396Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.BalabanSelectedSourceNativeMajorantRound396Exact as R396

pointwiseGeometricReproofPruned :
  R396.pointwiseSourceGeometricBoundIndependentLeaf ≡ false
pointwiseGeometricReproofPruned =
  R396.pointwiseSourceGeometricBoundIndependentLeafIsFalse

shellAttachmentStillPhysical :
  R396.selectedSourceEnvelopeShellAttachmentStillProofBearing ≡ true
shellAttachmentStillPhysical =
  R396.selectedSourceEnvelopeShellAttachmentStillProofBearingIsTrue

oneSidedGeometryStillPhysical :
  R396.oneSidedSourceDistanceStillProofBearing ≡ true
oneSidedGeometryStillPhysical = R396.oneSidedSourceDistanceStillProofBearingIsTrue

noClayPromotion : R396.clayPromotion ≡ false
noClayPromotion = R396.clayPromotionIsFalse
