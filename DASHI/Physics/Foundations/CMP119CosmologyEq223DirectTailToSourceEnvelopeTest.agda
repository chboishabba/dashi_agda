{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223DirectTailToSourceEnvelopeTest where

import DASHI.Physics.Foundations.CMP119CosmologyEq223DirectTailToSourceEnvelopeExact as Subject

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

finiteEq223UpperCompilesIntoEnvelope :
  Subject.eq223FiniteUpperCompilesIntoR136SourceEnvelope ≡ true
finiteEq223UpperCompilesIntoEnvelope = refl

finiteDGammaNotTerminalAfterEnvelopeCompilation :
  Subject.finiteDGammaRemainsTerminalConsumerCoordinate ≡ false
finiteDGammaNotTerminalAfterEnvelopeCompilation = refl
