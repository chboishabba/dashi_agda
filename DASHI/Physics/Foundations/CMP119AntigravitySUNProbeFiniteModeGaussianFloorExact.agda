{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySUNProbeFiniteModeGaussianFloorExact where

------------------------------------------------------------------------
-- DIRECT LITERAL SU(N) WILSON PROBE -> CMP119 CORRECTED RG EDGE LOWER BOUND
--
-- This compiler deliberately DOES NOT require the selected source product
-- postulate (-c)g^2=1. It derives c=-u from the literal SU(N) Wilson action
-- exponent at a nonzero source plaquette probe, transports the CMP109
-- finite-mode quartic-absorption bound to that same selected action's
-- E/R/B/vacuum-corrected projected RG edge, and retains explicit hypotheses
-- for the selected mode enclosures and source exponent evaluation.
--
-- It is a mathematical implication, not a proof that a published CMP119
-- finite measure has been instantiated by the literal Wilson probe.
--
-- Original sources: Wilson (1974), Bałaban CMP109 (1987), CMP119 (1988).
-- DASHI: same-source probe coefficient extraction and finite-mode transfer.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base as ℚ using
  (ℚ; Positive; _+_; _-_; _*_; _≤_; -_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieLatticeGauge using (GaugeField)
open import DASHI.Physics.YangMills.SUNMatrixCarrier using
  (CertifiedSUNMatrixTheory; SUNMatrixElement)

import DASHI.Physics.YangMills.BalabanClayT4SUNWilsonActionConventionExact as Literal
import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as CMP119
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as CMP109
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as Finite
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaLowerRemainderExact as Local
import DASHI.Physics.Foundations.CMP119AntigravitySUNLiteralProbeWilsonNormalizationExact as Probe
import DASHI.Physics.Foundations.CMP119AntigravitySUNLiteralProbePublishedEdgeExact as LiteralEdge
import DASHI.Physics.Foundations.CMP119AntigravitySelectedSourceEq223SectorProjectionExact as Source

module _
  {N : Nat}
  {Matrix Complex Vertex Mode Atom : Set}
  {theory : CertifiedSUNMatrixTheory N Matrix Complex}
  {Edge : Vertex → Vertex → Set}
  {trajectory : CMP109.SourceNormalizedCouplingTrajectory}
  (finiteMode : Finite.FiniteModeBetaTrajectoryData trajectory Mode Atom)
  {Density Background Fluctuation : Set}
  (selected : CMP119.CMP119Section2SourceNativeState
    Density Background Fluctuation
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction)
  (actionMeaning : Source.SelectedEq223RationalActionInterpretation selected)
  (literalAt : Nat → Literal.ScaledSUNWilsonActionData {Scalar = ℚ} theory Edge)
  (probeAt : Nat → GaugeField {G = SUNMatrixElement theory} Edge)
  (literalMultiplication : ∀ k x y →
    Literal.multiply (literalAt k) x y ≡ x * y)
  (probePositive : ∀ k →
    Positive (Probe.positiveCost (literalAt k) (probeAt k)))
  (literalInverseSameCMP109 : ∀ k →
    Literal.inverseCouplingSq (literalAt k)
    ≡ CMP109.inverseCoupling trajectory k)
  (sourceWilsonExponentAtProbe : ∀ k →
    CMP119.wilsonCoefficient selected k
      * Probe.positiveCost (literalAt k) (probeAt k)
    ≡ - Literal.scaledWilsonAction (literalAt k) (probeAt k))
  where

  betaIsSelectedLiteralProbeEdge :
    ∀ k →
    CMP109.beta trajectory (suc k)
      ≡ - Source.selectedProjectedEdge selected k
        + (Source.sectorProjection selected k
        - Source.sectorProjection selected (suc k))
  betaIsSelectedLiteralProbeEdge =
    LiteralEdge.physicalSelectedBetaIsCorrectedCMP119Edge
      trajectory selected actionMeaning
      literalAt probeAt literalMultiplication probePositive
      literalInverseSameCMP109 sourceWilsonExponentAtProbe

  finiteGaussianHalfFloor :
    ∀ k →
    Local.half * Local.computedGaussianLower
      (Finite.gaussianAt finiteMode k)
    ≤ CMP109.beta trajectory (suc k)
  finiteGaussianHalfFloor k =
    let
      gaussian = Finite.gaussianAt finiteMode k
      interaction = Finite.interactionAt finiteMode k
      splitBound :
        Local.half * Local.computedGaussianLower gaussian
        ≤ Local.betaZ gaussian + Local.betaInt interaction
      splitBound =
        Local.betaSplitLowerAfterQuarticAbsorption
          gaussian interaction
          (Finite.gamma finiteMode k)
          (Finite.interactionCouplingNonnegative finiteMode k)
          (Finite.gammaNonnegative finiteMode k)
          (Finite.interactionCouplingBelowGamma finiteMode k)
          (Finite.interactionCoefficientTotalNonnegative finiteMode k)
          (Finite.quarticAbsorption finiteMode k)
    in
    subst
      (λ target →
        Local.half * Local.computedGaussianLower gaussian ≤ target)
      (sym (Finite.sourceBetaSplitExact finiteMode k))
      splitBound

  selectedCorrectedLiteralEdgeGaussianHalfFloor :
    ∀ k →
    Local.half * Local.computedGaussianLower
      (Finite.gaussianAt finiteMode k)
    ≤ - Source.selectedProjectedEdge selected k
      + (Source.sectorProjection selected k
      - Source.sectorProjection selected (suc k))
  selectedCorrectedLiteralEdgeGaussianHalfFloor k =
    subst
      (λ target →
        Local.half * Local.computedGaussianLower
          (Finite.gaussianAt finiteMode k) ≤ target)
      (betaIsSelectedLiteralProbeEdge k)
      (finiteGaussianHalfFloor k)
