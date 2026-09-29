{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityP3GPhysicalProducerMinCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import Real as Bishop

import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as SU2
import DASHI.Physics.Foundations.CMP119AntigravityP3LiteralEdgeIncrementMinCutExact as Edge
import DASHI.Physics.Foundations.CMP119AntigravityP3UVAnchorFromSharedCouplingExact as UVAnchor
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact as P3
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- P3G PHYSICAL PRODUCER MIN-CUT
--
-- P3A--F do not define the P3G running-coupling remainder.  The P3G record
-- itself exposes an abstract `remainder` plus a bound, but no theorem tying
-- that remainder to the localized one-step effective-action coefficient.
--
-- For the antigravity S4 route the minimal physical producer therefore needs
-- exactly two source-facing semantic laws:
--
--   (A) its initial inverse-square coordinate is the inverse square of the
--       SAME beta-history coupling g_0;
--
--   (B) its positive-edge remainder is the SAME regular+interaction remainder
--       used by the literal/rich T4 one-step coefficient.
--
-- No all-depth state equality and no total-beta equality appear here.
------------------------------------------------------------------------

record P3GPhysicalProducerMinCut
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {split}
    (history : History.BetaSplitInverseSquareTerminalHistoryData
      trajectory split)
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat)
    (rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ)
    (running : SU2.CanonicalBishopSU2RunningInputs Nat)
    (geometry : Edge.CanonicalP3LiteralEdgeGeometry dataSet rich running)
    : Set₁ where
  field
    -- Payment A: one physical initial normalization.
    initialInverseSquareUsesSameCoupling :
      UVAnchor.P3InitialInverseSquareUsesHistoryCoupling history running

    -- Payment B: one local physical remainder law at every positive edge.
    positiveEdgeRemainderIsPhysical :
      ∀ depth →
      Bishop._≃_
        (P3.remainder (SU2.recursion running) (suc depth))
        (Rich.add rich
          (Rich.regularRemainder rich depth)
          (UV.embed (Literal.literalBetaInt dataSet depth)))

open P3GPhysicalProducerMinCut public

initialStateSameSource :
  ∀ {trajectory split history dataSet rich running geometry} →
  P3GPhysicalProducerMinCut
    {trajectory = trajectory} {split = split}
    history dataSet rich running geometry →
  Bishop._≃_
    (P3.inverseCouplingSq (SU2.recursion running) zero)
    (UV.embed (Flow.inverseCoupling trajectory zero))
initialStateSameSource producer =
  UVAnchor.p3InitialInverseCouplingSameSource
    (initialInverseSquareUsesSameCoupling producer)

positiveEdgeTotalIncrementSameLiteral :
  ∀ {trajectory split history dataSet rich running geometry}
    (producer : P3GPhysicalProducerMinCut
      {trajectory = trajectory} {split = split}
      history dataSet rich running geometry)
    depth →
  Bishop._≃_
    (Bishop._+_
      (P3.betaLogBlocking (SU2.recursion running) (suc depth))
      (P3.remainder (SU2.recursion running) (suc depth)))
    (UV.embed (Literal.literalBetaStep dataSet depth))
positiveEdgeTotalIncrementSameLiteral
    {geometry = geometry} producer depth =
  Edge.remainderImpliesTotalIncrement
    geometry depth (positiveEdgeRemainderIsPhysical producer depth)

allDepthStateEqualityIsProducerInput : Bool
allDepthStateEqualityIsProducerInput = false

totalIncrementEqualityIsProducerInput : Bool
totalIncrementEqualityIsProducerInput = false

initialSharedCouplingLawIsProducerInput : Bool
initialSharedCouplingLawIsProducerInput = true

localPhysicalRemainderLawIsProducerInput : Bool
localPhysicalRemainderLawIsProducerInput = true

allDepthStateEqualityIsProducerInputIsFalse :
  allDepthStateEqualityIsProducerInput ≡ false
allDepthStateEqualityIsProducerInputIsFalse = refl

totalIncrementEqualityIsProducerInputIsFalse :
  totalIncrementEqualityIsProducerInput ≡ false
totalIncrementEqualityIsProducerInputIsFalse = refl

p3GPhysicalProducerMinCutCompilerLevel : ProofLevel
p3GPhysicalProducerMinCutCompilerLevel = machineChecked

p3GInitialSharedCouplingPhysicalLevel : ProofLevel
p3GInitialSharedCouplingPhysicalLevel = conditional

p3GLocalRemainderPhysicalLevel : ProofLevel
p3GLocalRemainderPhysicalLevel = conditional
