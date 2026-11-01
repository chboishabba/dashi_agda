{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityBareSU2VsT4CouplingProbeExact where

------------------------------------------------------------------------
-- CROSS-PR PHYSICAL FACTOR-FOUR FIREWALL
--
-- A source action called 'u W+' by T4's literal SUN convention can agree
-- with the standard bare SU(2) normalization '4 u_bare W+' at any actual
-- strictly positive Wilson-cost probe ONLY WHEN u = 4 u_bare.
--
-- If one instead works with the Gibbs EXPONENT (negative action), the same
-- unit-positive-cost basis has source coefficient c = -4 u_bare.
--
-- The opposite basis W- = -W+ gives positive-action coefficient -4u_bare.
-- These are distinct sign conventions; no physical g_0=g_RG identification
-- follows from the algebra or the equality of one-loop beta coefficients.
--
-- The selected nonzero probe must be constructed from the literal lattice
-- field carrier before treating this as a physical source identification.
--
-- Attribution: Wilson (1974), DOI 10.1103/PhysRevD.10.2445;
-- Dashen--Gross (1981), DOI 10.1103/PhysRevD.23.2340.
-- DASHI: positive-probe coefficient uniqueness across T4 / standard SU2.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; Positive; _*_; -_)
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (trans; sym; cong)

open import DASHI.Physics.YangMills.CompactLieLatticeGauge using (GaugeField)
open import DASHI.Physics.YangMills.SUNMatrixCarrier using
  (CertifiedSUNMatrixTheory; SUNMatrixElement)

import DASHI.Physics.YangMills.BalabanClayT4SUNWilsonActionConventionExact as T4SUN
import DASHI.Physics.Foundations.CMP119AntigravityWilsonPlaquetteBasisOrientationExact as Basis
import DASHI.Physics.Foundations.CMP119AntigravitySUNLiteralProbeWilsonNormalizationExact as Probe
import DASHI.Physics.Foundations.CMP119AntigravitySelectedWilsonProductDeterminesSignExact as Cancel

module _
  {Matrix Complex Vertex : Set}
  {theory : CertifiedSUNMatrixTheory 2 Matrix Complex}
  {Edge : Vertex → Vertex → Set}
  (action : T4SUN.ScaledSUNWilsonActionData {Scalar = ℚ} theory Edge)
  (field : GaugeField {G = SUNMatrixElement theory} Edge)
  (costPositive : Positive (Probe.positiveCost action field))
  where

  literalCost : ℚ
  literalCost = Probe.positiveCost action field

  t4InverseMustBeFourBareInverse :
    ∀ t4Inverse bareInverse →
    t4Inverse * literalCost
      ≡ (Basis.four * bareInverse) * literalCost →
    t4Inverse ≡ Basis.four * bareInverse
  t4InverseMustBeFourBareInverse t4Inverse bareInverse samePhysicalAction =
    Cancel.cancelPositiveRightProduct
      t4Inverse (Basis.four * bareInverse) literalCost
      costPositive samePhysicalAction

  selectedGibbsExponentCoefficientIsMinusFourBareInverse :
    ∀ selectedCoefficient bareInverse →
    selectedCoefficient * literalCost
      ≡ - ((Basis.four * bareInverse) * literalCost) →
    selectedCoefficient ≡ - (Basis.four * bareInverse)
  selectedGibbsExponentCoefficientIsMinusFourBareInverse
      selectedCoefficient bareInverse literalExponent =
    Cancel.cancelPositiveRightProduct
      selectedCoefficient (- (Basis.four * bareInverse))
      literalCost costPositive
      (trans literalExponent (Ring.solve-∀ bareInverse literalCost))


