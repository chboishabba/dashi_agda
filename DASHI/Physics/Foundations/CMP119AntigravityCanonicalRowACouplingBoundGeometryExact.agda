{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowACouplingBoundGeometryExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (1ℚ; Positive; _*_; _≤_)

import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteSourceTrajectoryExact as Source
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalLiteralPlaquetteHistoryExact as CanonicalHistory
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowAInverseThresholdExact as Threshold
import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteTerminalHistoryExact as LiteralTerminal
import DASHI.Physics.Foundations.CMP119AntigravityCouplingCapToInverseThresholdExact as Converse
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4RationalInverseSquareOrderExact as Order
import DASHI.Physics.YangMills.BalabanYM4NonnegativeBetaFinitePropagationExact as Finite
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- ROW-A COUPLING CAP -> TERMINAL INVERSE THRESHOLD
--
-- Once the literal coupling is already known to lie below the canonical Row-A
-- gamma and both sides use the exact u g^2 = 1 representation, the terminal
-- inverse-threshold inequality is not an independent source datum.
------------------------------------------------------------------------

record CanonicalRowACouplingBoundGeometry
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat)
    (coherence : Source.LiteralPlaquetteUVChainCoherence dataSet)
    (source :
      CanonicalHistory.CanonicalLiteralPlaquetteHistory dataSet coherence)
    (rowA : RowA.FiniteQuarticResponseConstants) : Set₁ where
  field
    terminalScale : Nat

    ActiveScale : Nat → Set
    terminalActive : ActiveScale terminalScale

    gapToTerminal : ∀ scale → ActiveScale scale → Nat
    scaleReachesTerminal : ∀ scale (active : ActiveScale scale) →
      Finite.advance scale (gapToTerminal scale active) ≡ terminalScale

    couplingPositive : ∀ scale →
      Positive (LiteralTerminal.literalCouplingAt dataSet scale)

    couplingBelowCanonicalGamma : ∀ scale →
      LiteralTerminal.literalCouplingAt dataSet scale
      ≤ RowA.canonicalQuarticResponseGamma rowA

    inverseCouplingRepresentation : ∀ scale →
      Flow.inverseCoupling
        (CanonicalHistory.trajectory coherence) scale
      * Order.square (LiteralTerminal.literalCouplingAt dataSet scale)
      ≡ 1ℚ

open CanonicalRowACouplingBoundGeometry public

orderDataAt :
  ∀ {dataSet coherence source rowA} →
  CanonicalRowACouplingBoundGeometry dataSet coherence source rowA →
  Nat →
  Order.RationalInverseSquareOrderData
orderDataAt {dataSet = dataSet} {coherence = coherence} {rowA = rowA}
    geometry scale = record
  { Order.RationalInverseSquareOrderData.coupling =
      LiteralTerminal.literalCouplingAt dataSet scale
  ; Order.RationalInverseSquareOrderData.thresholdCoupling =
      RowA.canonicalQuarticResponseGamma rowA
  ; Order.RationalInverseSquareOrderData.inverseCoupling =
      Flow.inverseCoupling
        (CanonicalHistory.trajectory coherence) scale
  ; Order.RationalInverseSquareOrderData.inverseThreshold =
      Threshold.canonicalInverseThreshold rowA
  ; Order.RationalInverseSquareOrderData.couplingPositive =
      couplingPositive geometry scale
  ; Order.RationalInverseSquareOrderData.thresholdCouplingPositive =
      ℚ.positive (RowA.canonicalQuarticResponseGammaPositive rowA)
  ; Order.RationalInverseSquareOrderData.inverseCouplingTimesSquare =
      inverseCouplingRepresentation geometry scale
  ; Order.RationalInverseSquareOrderData.inverseThresholdTimesSquare =
      Threshold.canonicalInverseThresholdRepresentation rowA
  }

terminalInverseThresholdDerived :
  ∀ {dataSet coherence source rowA}
    (geometry :
      CanonicalRowACouplingBoundGeometry dataSet coherence source rowA) →
  Threshold.canonicalInverseThreshold rowA
  ≤ Flow.inverseCoupling
      (CanonicalHistory.trajectory coherence)
      (terminalScale geometry)
terminalInverseThresholdDerived geometry =
  Converse.smallCouplingImpliesInverseThreshold
    (orderDataAt geometry (terminalScale geometry))
    (couplingBelowCanonicalGamma geometry (terminalScale geometry))

asCanonicalRowATerminalGeometry :
  ∀ {dataSet coherence source rowA} →
  CanonicalRowACouplingBoundGeometry dataSet coherence source rowA →
  Threshold.CanonicalRowATerminalGeometry
    dataSet coherence source rowA
asCanonicalRowATerminalGeometry geometry = record
  { Threshold.CanonicalRowATerminalGeometry.terminalScale =
      terminalScale geometry
  ; Threshold.CanonicalRowATerminalGeometry.ActiveScale =
      ActiveScale geometry
  ; Threshold.CanonicalRowATerminalGeometry.terminalActive =
      terminalActive geometry
  ; Threshold.CanonicalRowATerminalGeometry.gapToTerminal =
      gapToTerminal geometry
  ; Threshold.CanonicalRowATerminalGeometry.scaleReachesTerminal =
      scaleReachesTerminal geometry
  ; Threshold.CanonicalRowATerminalGeometry.terminalInverseThreshold =
      terminalInverseThresholdDerived geometry
  ; Threshold.CanonicalRowATerminalGeometry.couplingPositive =
      couplingPositive geometry
  ; Threshold.CanonicalRowATerminalGeometry.inverseCouplingRepresentation =
      inverseCouplingRepresentation geometry
  }

freeTerminalInverseThresholdRequired : Bool
freeTerminalInverseThresholdRequired = false

freeTerminalInverseThresholdRequiredIsFalse :
  freeTerminalInverseThresholdRequired ≡ false
freeTerminalInverseThresholdRequiredIsFalse = refl

canonicalRowACouplingBoundGeometryCompilerLevel : ProofLevel
canonicalRowACouplingBoundGeometryCompilerLevel = machineChecked
