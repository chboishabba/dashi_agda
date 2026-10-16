module DASHI.Moonshine.Monster3BActualLinearIsotypicTerminalCompilerValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BActualLinearIsotypicTerminalCompilerExact as Terminal

hZetaCompilerReady : Terminal.hZetaRecognitionCompilerClosesAfterPacket Terminal.canonicalBoundary ≡ true
hZetaCompilerReady = refl

isotypicTailReady : Terminal.genericIsotypicTailSourceWritten Terminal.canonicalBoundary ≡ true
isotypicTailReady = refl

schurTailReady : Terminal.genericSchurMultiplicityTailSourceWritten Terminal.canonicalBoundary ≡ true
schurTailReady = refl

actualPacketStillOpen : Terminal.actualMonsterLinearInputPacketInhabitedHere Terminal.canonicalBoundary ≡ false
actualPacketStillOpen = refl

normalizerStillOpen : Terminal.actualSuzukiNormalizerActionPaidHere Terminal.canonicalBoundary ≡ false
normalizerStillOpen = refl
