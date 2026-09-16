module DASHI.Reasoning.PlatoSymposiumTransmissionAttributionRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Reasoning.PlatoSymposiumTransmissionAttributionExact as Bridge

immediateSpeakerDoesNotFixClaimRole :
  Bridge.immediateSpeakerDeterminesClaimRole
    Bridge.canonicalPlatoTransmissionAttributionBoundary ≡ false
immediateSpeakerDoesNotFixClaimRole = refl

historicalSpeakerIsNotFormalisationAuthor :
  Bridge.historicalSpeakerEqualsFormalisationAuthor
    Bridge.canonicalPlatoTransmissionAttributionBoundary ≡ false
historicalSpeakerIsNotFormalisationAuthor = refl

dramaticAttributionDoesNotCreateAuthority :
  Bridge.dramaticAttributionCreatesClaimAuthority
    Bridge.canonicalPlatoTransmissionAttributionBoundary ≡ false
dramaticAttributionDoesNotCreateAuthority = refl

transmissionPathIsRetained :
  Bridge.layeredTransmissionPathRetained
    Bridge.canonicalPlatoTransmissionAttributionBoundary ≡ true
transmissionPathIsRetained = refl

canonicalAttributionOwnersAreReused :
  Bridge.existingAttributionOwnersReused ≡ true
canonicalAttributionOwnersAreReused = refl
