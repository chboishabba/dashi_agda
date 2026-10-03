{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223R136SourceEnvelopeUpperTest where

import DASHI.Physics.Foundations.CMP119CosmologyEq223R136SourceEnvelopeUpperExact as Subject

open import Agda.Builtin.Bool using (Bool; true)

sourceEnvelopeEliminatesFiniteDGammaFromTerminalConsumer : Bool
sourceEnvelopeEliminatesFiniteDGammaFromTerminalConsumer =
  Subject.sourceEnvelopeTerminalConsumerNeedsFiniteDGamma

sourceEnvelopeUsesExistingRealWeakOrder : Bool
sourceEnvelopeUsesExistingRealWeakOrder =
  Subject.sourceEnvelopeUsesExistingRealWeakOrderAuthority
