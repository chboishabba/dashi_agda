{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyDirectSourceNumeratorTailToExpansionTest where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119CosmologyDirectSourceNumeratorTailToExpansionExact as Subject

directNumeratorMarginClosesPreferredSign :
  Subject.directSourceNumeratorTailMarginCompilesToMatterAcceleration ≡ true
directNumeratorMarginClosesPreferredSign = refl

noERBEnvelopeAtTerminal :
  Subject.directSourceNumeratorRouteNeedsCombinedERBEnvelope ≡ false
noERBEnvelopeAtTerminal = refl

noVacuumThresholdAtTerminal :
  Subject.directSourceNumeratorRouteNeedsVacuumThreshold ≡ false
noVacuumThresholdAtTerminal = refl

noFiniteFamilyAtTerminal :
  Subject.directSourceNumeratorRouteNeedsFiniteFamilyOrObservable ≡ false
noFiniteFamilyAtTerminal = refl
