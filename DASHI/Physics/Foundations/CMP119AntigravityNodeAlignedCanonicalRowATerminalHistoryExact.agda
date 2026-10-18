{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityNodeAlignedCanonicalRowATerminalHistoryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (_≤_)

import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteSourceTrajectoryExact as Source
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalLiteralPlaquetteHistoryExact as CanonicalHistory
import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteNodeCouplingExact as Node
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowAInverseThresholdExact as Threshold
import DASHI.Physics.Foundations.CMP119AntigravityCouplingCapToInverseThresholdExact as Converse
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4NonnegativeBetaFinitePropagationExact as Finite
import DASHI.Physics.YangMills.BalabanYM4RationalInverseSquareOrderExact as Order
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- CORRECTED NODE-ALIGNED CANONICAL ROW-A TERMINAL HISTORY
--
-- This is the preferred replacement for the earlier terminal adapter whose
-- coupling readout used the producer edge index directly as a source-node
-- index.
--
-- All inverse-square representation equations now come from the node-aligned
-- carrier:
--
--   node 0     : nextInverseCouplingSq 0 * g_0^2 = 1
--   node k + 1 : inverseCouplingSq k     * g_(k+1)^2 = 1
--
-- with g_(k+1) definitionally the producer current coupling at edge k.
------------------------------------------------------------------------

record NodeAlignedRowATerminalGeometry
    {dataSet}
    (coherence : Source.LiteralPlaquetteUVChainCoherence dataSet)
    (literalSource :
      CanonicalHistory.CanonicalLiteralPlaquetteHistory dataSet coherence)
    (nodeCoupling : Node.LiteralPlaquetteNodeCoupling dataSet coherence)
    (rowA : RowA.FiniteQuarticResponseConstants) : Set₁ where
  field
    terminalScale : Nat

    ActiveScale : Nat → Set
    terminalActive : ActiveScale terminalScale

    gapToTerminal : ∀ scale → ActiveScale scale → Nat
    scaleReachesTerminal : ∀ scale (active : ActiveScale scale) →
      Finite.advance scale (gapToTerminal scale active) ≡ terminalScale

    terminalCouplingBelowCanonicalGamma :
      Node.sourceCoupling nodeCoupling terminalScale
      ≤ RowA.canonicalQuarticResponseGamma rowA

open NodeAlignedRowATerminalGeometry public

orderDataAt :
  ∀ {dataSet coherence literalSource nodeCoupling rowA} →
  NodeAlignedRowATerminalGeometry
    coherence literalSource nodeCoupling rowA →
  Nat →
  Order.RationalInverseSquareOrderData
orderDataAt
    {dataSet = dataSet} {coherence = coherence}
    {nodeCoupling = nodeCoupling} {rowA = rowA}
    geometry scale = record
  { Order.RationalInverseSquareOrderData.coupling =
      Node.sourceCoupling nodeCoupling scale
  ; Order.RationalInverseSquareOrderData.thresholdCoupling =
      RowA.canonicalQuarticResponseGamma rowA
  ; Order.RationalInverseSquareOrderData.inverseCoupling =
      Source.sourceInverseCoupling dataSet scale
  ; Order.RationalInverseSquareOrderData.inverseThreshold =
      Threshold.canonicalInverseThreshold rowA
  ; Order.RationalInverseSquareOrderData.couplingPositive =
      Node.sourceCouplingPositive nodeCoupling scale
  ; Order.RationalInverseSquareOrderData.thresholdCouplingPositive =
      ℚ.positive (RowA.canonicalQuarticResponseGammaPositive rowA)
  ; Order.RationalInverseSquareOrderData.inverseCouplingTimesSquare =
      Node.sourceInverseSquareRepresentation nodeCoupling scale
  ; Order.RationalInverseSquareOrderData.inverseThresholdTimesSquare =
      Threshold.canonicalInverseThresholdRepresentation rowA
  }

terminalInverseThreshold :
  ∀ {dataSet coherence literalSource nodeCoupling rowA}
    (geometry :
      NodeAlignedRowATerminalGeometry
        coherence literalSource nodeCoupling rowA) →
  Threshold.canonicalInverseThreshold rowA
  ≤ Source.sourceInverseCoupling dataSet (terminalScale geometry)
terminalInverseThreshold geometry =
  Converse.smallCouplingImpliesInverseThreshold
    (orderDataAt geometry (terminalScale geometry))
    (terminalCouplingBelowCanonicalGamma geometry)

asBetaSplitInverseSquareTerminalHistory :
  ∀ {dataSet coherence literalSource nodeCoupling rowA} →
  NodeAlignedRowATerminalGeometry
    coherence literalSource nodeCoupling rowA →
  History.BetaSplitInverseSquareTerminalHistoryData
    (CanonicalHistory.trajectory coherence)
    (CanonicalHistory.compiledSplit literalSource)
asBetaSplitInverseSquareTerminalHistory
    {nodeCoupling = nodeCoupling} {rowA = rowA}
    geometry = record
  { History.BetaSplitInverseSquareTerminalHistoryData.couplingAt =
      Node.sourceCoupling nodeCoupling
  ; History.BetaSplitInverseSquareTerminalHistoryData.gamma =
      RowA.canonicalQuarticResponseGamma rowA
  ; History.BetaSplitInverseSquareTerminalHistoryData.inverseThreshold =
      Threshold.canonicalInverseThreshold rowA
  ; History.BetaSplitInverseSquareTerminalHistoryData.terminalScale =
      terminalScale geometry
  ; History.BetaSplitInverseSquareTerminalHistoryData.ActiveScale =
      ActiveScale geometry
  ; History.BetaSplitInverseSquareTerminalHistoryData.terminalActive =
      terminalActive geometry
  ; History.BetaSplitInverseSquareTerminalHistoryData.gapToTerminal =
      gapToTerminal geometry
  ; History.BetaSplitInverseSquareTerminalHistoryData.scaleReachesTerminal =
      scaleReachesTerminal geometry
  ; History.BetaSplitInverseSquareTerminalHistoryData.terminalInverseThreshold =
      terminalInverseThreshold geometry
  ; History.BetaSplitInverseSquareTerminalHistoryData.couplingPositive =
      Node.sourceCouplingPositive nodeCoupling
  ; History.BetaSplitInverseSquareTerminalHistoryData.gammaPositive =
      ℚ.positive (RowA.canonicalQuarticResponseGammaPositive rowA)
  ; History.BetaSplitInverseSquareTerminalHistoryData.inverseCouplingRepresentation =
      Node.sourceInverseSquareRepresentation nodeCoupling
  ; History.BetaSplitInverseSquareTerminalHistoryData.inverseThresholdRepresentation =
      Threshold.canonicalInverseThresholdRepresentation rowA
  }

sameIndexEdgeCouplingTerminalAdapterPreferred : Bool
sameIndexEdgeCouplingTerminalAdapterPreferred = false

nodeAlignedTerminalAdapterPreferred : Bool
nodeAlignedTerminalAdapterPreferred = true

sameIndexEdgeCouplingTerminalAdapterPreferredIsFalse :
  sameIndexEdgeCouplingTerminalAdapterPreferred ≡ false
sameIndexEdgeCouplingTerminalAdapterPreferredIsFalse = refl

nodeAlignedTerminalAdapterPreferredIsTrue :
  nodeAlignedTerminalAdapterPreferred ≡ true
nodeAlignedTerminalAdapterPreferredIsTrue = refl

nodeAlignedCanonicalRowATerminalCompilerLevel : ProofLevel
nodeAlignedCanonicalRowATerminalCompilerLevel = machineChecked
