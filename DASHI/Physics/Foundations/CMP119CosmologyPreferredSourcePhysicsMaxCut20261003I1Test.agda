{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261003I1Test where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261003I1Exact as Subject

fourPreferredLeavesRemain :
  Subject.preferredSourcePhysicsResidualCount ≡ 4
fourPreferredLeavesRemain = refl

b2IsOnePointPartitionTailDominance :
  Subject.b2TerminalLeafIsPartitionDerivativeTailDominance ≡ true
b2IsOnePointPartitionTailDominance = refl

connectedTraceDoesNotPayB2 :
  Subject.connectedOrderedHaarTracePaysB2Directly ≡ false
connectedTraceDoesNotPayB2 = refl

lateScaleEliminationNotYetClaimed :
  Subject.tailDecayAloneEliminatesB2AtCurrentB1Interface ≡ false
lateScaleEliminationNotYetClaimed = refl
