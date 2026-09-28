{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowAInverseThresholdExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; Positive; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteSourceTrajectoryExact as Source
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalLiteralPlaquetteHistoryExact as CanonicalHistory
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowALiteralTerminalHistoryExact as Terminal
import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteTerminalHistoryExact as LiteralTerminal
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quot
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4RationalInverseSquareOrderExact as Order
import DASHI.Physics.YangMills.BalabanYM4NonnegativeBetaFinitePropagationExact as Finite
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- CANONICAL ROW-A INVERSE THRESHOLD
--
-- The previous terminal-history interface accepted both
--
--   inverseThreshold
--   inverseThreshold * gamma^2 = 1
--
-- as source data.  But Row-A already proves gamma > 0 and the repository
-- already vendors exact positive rational reciprocal machinery.
--
-- Therefore define, rather than postulate,
--
--   u_* := 1 / gamma^2.
------------------------------------------------------------------------

gamma :
  RowA.FiniteQuarticResponseConstants → ℚ
gamma = RowA.canonicalQuarticResponseGamma

gammaSquare :
  RowA.FiniteQuarticResponseConstants → ℚ
gammaSquare rowA = Order.square (gamma rowA)

gammaSquarePositive :
  ∀ rowA → 0ℚ < gammaSquare rowA
gammaSquarePositive rowA =
  let
    g = gamma rowA
    instance
      gPositive : Positive g
      gPositive = ℚ.positive (RowA.canonicalQuarticResponseGammaPositive rowA)
      gSquarePositive : Positive (g * g)
      gSquarePositive = ℚP.pos*pos⇒pos g g
  in
  ℚP.positive⁻¹ (g * g)

canonicalInverseThreshold :
  RowA.FiniteQuarticResponseConstants → ℚ
canonicalInverseThreshold rowA =
  Quot.positiveReciprocal
    (gammaSquare rowA)
    (gammaSquarePositive rowA)

canonicalInverseThresholdRepresentation :
  ∀ rowA →
  canonicalInverseThreshold rowA * gammaSquare rowA ≡ 1ℚ
canonicalInverseThresholdRepresentation rowA =
  trans
    (ℚP.*-comm
      (canonicalInverseThreshold rowA)
      (gammaSquare rowA))
    (Quot.positiveReciprocalRightInverse
      (gammaSquare rowA)
      (gammaSquarePositive rowA))

canonicalInverseThresholdPositive :
  ∀ rowA → 0ℚ < canonicalInverseThreshold rowA
canonicalInverseThresholdPositive rowA =
  Quot.positiveReciprocalPositive
    (gammaSquare rowA)
    (gammaSquarePositive rowA)

------------------------------------------------------------------------
-- The remaining terminal-history content is now geometry/physical coupling
-- data only.  The threshold scalar and its inverse-square law are compiled.
------------------------------------------------------------------------

record CanonicalRowATerminalGeometry
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

    terminalInverseThreshold :
      canonicalInverseThreshold rowA
      ≤ Flow.inverseCoupling
          (CanonicalHistory.trajectory coherence)
          terminalScale

    couplingPositive : ∀ scale →
      Positive (LiteralTerminal.literalCouplingAt dataSet scale)

    inverseCouplingRepresentation : ∀ scale →
      Flow.inverseCoupling
        (CanonicalHistory.trajectory coherence) scale
      * Order.square (LiteralTerminal.literalCouplingAt dataSet scale)
      ≡ 1ℚ

open CanonicalRowATerminalGeometry public

asCanonicalRowALiteralTerminalHistory :
  ∀ {dataSet coherence source rowA} →
  CanonicalRowATerminalGeometry dataSet coherence source rowA →
  Terminal.CanonicalRowALiteralTerminalHistory
    dataSet coherence source rowA
asCanonicalRowALiteralTerminalHistory {rowA = rowA} geometry = record
  { Terminal.CanonicalRowALiteralTerminalHistory.inverseThreshold =
      canonicalInverseThreshold rowA
  ; Terminal.CanonicalRowALiteralTerminalHistory.terminalScale =
      terminalScale geometry
  ; Terminal.CanonicalRowALiteralTerminalHistory.ActiveScale =
      ActiveScale geometry
  ; Terminal.CanonicalRowALiteralTerminalHistory.terminalActive =
      terminalActive geometry
  ; Terminal.CanonicalRowALiteralTerminalHistory.gapToTerminal =
      gapToTerminal geometry
  ; Terminal.CanonicalRowALiteralTerminalHistory.scaleReachesTerminal =
      scaleReachesTerminal geometry
  ; Terminal.CanonicalRowALiteralTerminalHistory.terminalInverseThreshold =
      terminalInverseThreshold geometry
  ; Terminal.CanonicalRowALiteralTerminalHistory.couplingPositive =
      couplingPositive geometry
  ; Terminal.CanonicalRowALiteralTerminalHistory.inverseCouplingRepresentation =
      inverseCouplingRepresentation geometry
  ; Terminal.CanonicalRowALiteralTerminalHistory.inverseThresholdRepresentation =
      canonicalInverseThresholdRepresentation rowA
  }

freeInverseThresholdRequired : Bool
freeInverseThresholdRequired = false

freeInverseThresholdRepresentationRequired : Bool
freeInverseThresholdRepresentationRequired = false

freeInverseThresholdRequiredIsFalse :
  freeInverseThresholdRequired ≡ false
freeInverseThresholdRequiredIsFalse = refl

freeInverseThresholdRepresentationRequiredIsFalse :
  freeInverseThresholdRepresentationRequired ≡ false
freeInverseThresholdRepresentationRequiredIsFalse = refl

canonicalRowAInverseThresholdCompilerLevel : ProofLevel
canonicalRowAInverseThresholdCompilerLevel = machineChecked
