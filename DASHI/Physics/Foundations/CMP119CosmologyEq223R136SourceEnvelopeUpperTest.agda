{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223R136SourceEnvelopeUpperTest where

import DASHI.Physics.Foundations.CMP119CosmologyEq223R136SourceEnvelopeUpperExact as Subject

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

sourceEnvelopeEliminatesFiniteDGammaFromTerminalConsumer :
  Subject.sourceEnvelopeTerminalConsumerNeedsFiniteDGamma ≡ false
sourceEnvelopeEliminatesFiniteDGammaFromTerminalConsumer = refl

sourceEnvelopeUsesExistingRealWeakOrder :
  Subject.sourceEnvelopeUsesExistingRealWeakOrderAuthority ≡ true
sourceEnvelopeUsesExistingRealWeakOrder = refl

sourceEnvelopeAddsNoPhysicalPremise :
  Subject.sourceEnvelopeAddsNewPhysicalPremise ≡ false
sourceEnvelopeAddsNoPhysicalPremise = refl
