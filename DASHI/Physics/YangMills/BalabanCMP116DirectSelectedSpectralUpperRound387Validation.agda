{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116DirectSelectedSpectralUpperRound387Validation where

import DASHI.Physics.YangMills.BalabanCMP116DirectSelectedSpectralUpperRound387Exact as R387

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true)

_directSelectedSpectralUpperIsTerminalConsumer :
  R387.directSelectedSpectralUpperIsTerminalConsumer ≡ true
_directSelectedSpectralUpperIsTerminalConsumer = refl

_sourceEnvelopeNotMandatoryAtTerminalABI :
  R387.sourceEnvelopeNotMandatoryAtTerminalABI ≡ true
_sourceEnvelopeNotMandatoryAtTerminalABI = refl

_round387CompilerConsumesDirectUpper :
  R387.round387CompilerConsumesDirectUpper ≡ true
_round387CompilerConsumesDirectUpper = refl
