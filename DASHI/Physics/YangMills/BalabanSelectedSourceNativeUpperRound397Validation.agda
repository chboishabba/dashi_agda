{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSelectedSourceNativeUpperRound397Validation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (refl)

import DASHI.Physics.YangMills.BalabanSelectedSourceNativeUpperRound397Exact as R397

round397EqualityPruned :
  R397.selectedSourceEnvelopeShellEqualityRequired ≡ false
round397EqualityPruned = refl

round397UpperAttachmentRetained :
  R397.selectedSourceEnvelopeUpperAttachmentStillProofBearing ≡ true
round397UpperAttachmentRetained = refl

round397MajorantRetained :
  R397.sourceNativeGeometricMajorantStillProofBearing ≡ true
round397MajorantRetained = refl

round397DistanceRetained :
  R397.oneSidedSourceDistanceStillProofBearing ≡ true
round397DistanceRetained = refl

round397NoClayPromotion : R397.clayPromotion ≡ false
round397NoClayPromotion = refl
