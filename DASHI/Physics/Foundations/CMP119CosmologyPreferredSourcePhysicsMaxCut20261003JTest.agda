{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261003JTest where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261003JExact as Subject

fourPreferredLeavesRemain : Subject.preferredSourcePhysicsResidualCount ≡ 4
fourPreferredLeavesRemain = refl

a1IsSevenGeneratorChecks : Subject.a1LiteralGeneratorCheckCount ≡ 7
a1IsSevenGeneratorChecks = refl

b2IsOnePointPartitionTailDominance :
  Subject.b2TerminalLeafIsPartitionDerivativeTailDominance ≡ true
b2IsOnePointPartitionTailDominance = refl

b2HasCorrectPartitionResponseBudgetCompiler :
  Subject.b2PartitionResponseHasTwoBoundCompiler ≡ true
b2HasCorrectPartitionResponseBudgetCompiler = refl

connectedTraceStillDoesNotPayB2 :
  Subject.connectedOrderedHaarTracePaysB2Directly ≡ false
connectedTraceStillDoesNotPayB2 = refl

adapterDebtStillZero : Subject.remainingAdapterConstructionCount ≡ 0
adapterDebtStillZero = refl
