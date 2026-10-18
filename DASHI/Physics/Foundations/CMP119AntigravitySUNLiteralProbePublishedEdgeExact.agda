{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySUNLiteralProbePublishedEdgeExact where

------------------------------------------------------------------------
-- CMP119 SELECTED RG EDGE DIRECTLY FROM LITERAL YM #1049 SU(N) WILSON DATA
--
-- This does NOT use the extra (-c)g^2=1 premise from the previous S4
-- approach. Instead the physical normalization debt is:
--  (i) source exponent's Wilson term at one actual positive-cost field,
-- (ii) same source coefficient u and selected CMP109 inverse coupling.
-- The selected four E/R/B/vacuum terms and Eq.(2.23) remain THE SAME
-- source object in the output.
--
-- The field probe cannot be chosen by declaring a source coefficient. Its
-- positive cost and exponent evaluation must come from the literal SU(N)
-- Wilson action and the published CMP119 finite-measure definition.
--
-- Wilson (1974), DOI 10.1103/PhysRevD.10.2445;
-- Bałaban CMP119 (1988), DOI 10.1007/BF01217741.
-- DASHI's cross-PR direct finite source normalization adapter.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base as ℚ using (ℚ; Positive; _+_; _-_; _*_; -_)

open import DASHI.Physics.YangMills.CompactLieLatticeGauge using (GaugeField)
open import DASHI.Physics.YangMills.SUNMatrixCarrier using
  (CertifiedSUNMatrixTheory; SUNMatrixElement)

import DASHI.Physics.YangMills.BalabanClayT4SUNWilsonActionConventionExact as Literal
import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as CMP119
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as CMP109
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.Foundations.CMP119AntigravitySUNLiteralProbeWilsonNormalizationExact as Probe
import DASHI.Physics.Foundations.CMP119AntigravitySelectedSourceEq223SectorProjectionExact as Source

module _
  {N : Nat}
  {Matrix Complex Vertex : Set}
  {theory : CertifiedSUNMatrixTheory N Matrix Complex}
  {Edge : Vertex → Vertex → Set}
  (trajectory : CMP109.SourceNormalizedCouplingTrajectory)
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
    Positive
      (Probe.positiveCost (literalAt k) (probeAt k)))
  (literalSourceInverseIsCMP109 : ∀ k →
    Literal.inverseCouplingSq (literalAt k)
    ≡ CMP109.inverseCoupling trajectory k)
  (selectedWilsonExponentIsLiteralAtProbe : ∀ k →
    CMP119.wilsonCoefficient selected k
    * Probe.positiveCost (literalAt k) (probeAt k)
    ≡ - Literal.scaledWilsonAction (literalAt k) (probeAt k))
  where

  literalProbeDeterminesSelectedWilson :
    ∀ k →
    CMP119.wilsonCoefficient selected k
    ≡ - CMP109.inverseCoupling trajectory k
  literalProbeDeterminesSelectedWilson k =
    Probe.selectedSourceExponentProbeDeterminesCMP109Wilson
      (literalAt k)
      (literalMultiplication k)
      selected trajectory k
      (literalSourceInverseIsCMP109 k)
      (probeAt k)
      (probePositive k)
      (selectedWilsonExponentIsLiteralAtProbe k)

  physicalSelectedBetaIsCorrectedCMP119Edge :
    ∀ k →
    CMP109.beta trajectory (suc k)
    ≡ - Source.selectedProjectedEdge selected k
      + (Source.sectorProjection selected k
      - Source.sectorProjection selected (suc k))
  physicalSelectedBetaIsCorrectedCMP119Edge =
    Source.selectedSourceNegativeWilsonBeta
      selected actionMeaning trajectory literalProbeDeterminesSelectedWilson
