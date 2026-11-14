module DASHI.Moonshine.OggSSPClimbingGymExactHoleAnalyticBridgeValidation where

open import DASHI.Core.Prelude

import DASHI.Moonshine.OggSSPClimbingGymExactHoleAnalyticBridge as Bridge

exactHoleObserverNoLongerUsesRealFloor :
  Bridge.holeAddressUsesExactNatRadixCodec
    Bridge.canonicalExactHoleAnalyticBridgeBoundary
  ≡ true
exactHoleObserverNoLongerUsesRealFloor = refl

arbitraryPhaseQuantiserStillSeparate :
  Bridge.arbitraryHeightPhaseQuantiserStillSeparate
    Bridge.canonicalExactHoleAnalyticBridgeBoundary
  ≡ true
arbitraryPhaseQuantiserStillSeparate = refl
