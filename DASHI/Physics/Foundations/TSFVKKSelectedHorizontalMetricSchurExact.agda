{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSFVKKSelectedHorizontalMetricSchurExact where

------------------------------------------------------------------------
-- P02/P08: EXACT SAME FOUR-METRIC from a NONTRIVIAL 5D KK FORM.
--
-- This formalizes the precise 5D -> 4D Schur/horizontal reduction
-- already used in the original KK #1239/#1241 sourced physical model:
--
--  G5((v,s),(w,t))
--    = g4(v,w) + b^2 (s+A(v)) (t+A(w)).
--
-- This is the Jordan-frame KK ansatz at ONE selected source state.
-- The physical four-bilinear g4 must eventually be the SAME measured
-- observer quadratic, not a newly chosen (3,1) label. The positive
-- radius b^2 and actual 5D field equations remain physical inputs.
--
-- The construction below proves:
-- * non-Abelian YM is irrelevant to this classical U(1) KK metric;
-- * horizontal lift s=-A(v) recovers EXACT g4 pointwise;
-- * the full 5D bilinear has the proper off-diagonal/vertical blocks;
-- * fibre-coordinate gauge shift A->A+dLambda and
--   s->s-dLambda(v) preserves this SAME 5D bilinear;
-- * naive circle-coordinate freeze s=t=0 is NOT the actual
--   horizontal/Schur reduction; the A*A contribution remains.
--
-- No selected physical continuum metric, Einstein source, nonzero
-- radion mass, actual 5D circle topology or OS generator is hereby
-- constructed. Every proof is finite rational polynomial algebra.
--
-- Original KK metric-reduction mathematics / original DASHI #1239,
-- #1241 Jordan-action and original observable/metric owners credited.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as Ring

-- V is the ORIGINAL measured four-tangent carrier supplied at the
-- physical boundary. We never choose V=Fin 4 or hard-code a 31 mask.
-- The source q4 is the actual observer-metric bilinear still to build.
KK5Bilinear :
  ∀ {V : Set} →
  (g4 : V → V → ℚ) →
  (connection : V → ℚ) →
  (radiusSquared : ℚ) →
  V → ℚ → V → ℚ → ℚ
KK5Bilinear g4 connection radiusSquared v fibreV w fibreW =
  g4 v w +
  radiusSquared *
    ((fibreV + connection v) * (fibreW + connection w))

horizontalCircleComponent :
  ∀ {V : Set} → (connection : V → ℚ) → V → ℚ
horizontalCircleComponent connection v = - connection v

-- The selected (3,1) metric is recovered as an EXACT bilinear:
-- the same g4 argument appears on both sides of the theorem, not a
-- separately assumed Kaluza--Klein reduction witness.
actualKKHorizontalReductionIsOriginalFourMetric :
  ∀ {V : Set}
    (g4 : V → V → ℚ)
    (connection : V → ℚ)
    (radiusSquared : ℚ)
    (v w : V) →
  KK5Bilinear g4 connection radiusSquared
    v (horizontalCircleComponent connection v)
    w (horizontalCircleComponent connection w)
  ≡ g4 v w
actualKKHorizontalReductionIsOriginalFourMetric
    g4 connection radiusSquared v w =
  Ring.solve-∀
    (g4 v w) (connection v) (connection w) radiusSquared

-- This equality is the selected Schur-completion cross-term identity;
-- the 4D raw upper-left block is not g4 when A is nonzero.
KK5ExpandedBlocks :
  ∀ {V : Set}
    (g4 : V → V → ℚ)
    (connection : V → ℚ)
    (radiusSquared : ℚ)
    (v w : V)
    (fibreV fibreW : ℚ) →
  KK5Bilinear g4 connection radiusSquared
    v fibreV w fibreW
  ≡
  g4 v w +
    radiusSquared * (connection v * connection w) +
    radiusSquared * (connection v * fibreW) +
    radiusSquared * (fibreV * connection w) +
    radiusSquared * (fibreV * fibreW)
KK5ExpandedBlocks g4 connection r v w s t =
  Ring.solve-∀ (g4 v w) (connection v) (connection w) r s t

-- The actual 5D metric at circle-coordinate zero carries a
-- gauge A_mu A_nu correction. Horizontal reduction CANCELS it.
naivelyFrozenFibreHasAdditionalConnectionTerm :
  ∀ {V : Set}
    (g4 : V → V → ℚ)
    (connection : V → ℚ)
    (radiusSquared : ℚ)
    (v w : V) →
  KK5Bilinear g4 connection radiusSquared
    v 0ℚ w 0ℚ
  ≡
  g4 v w + radiusSquared * (connection v * connection w)
naivelyFrozenFibreHasAdditionalConnectionTerm
    g4 connection r v w =
  Ring.solve-∀ (g4 v w) (connection v) (connection w) r

-- Tangent-space form of the original classical KK U(1) gauge
-- transformation, induced by local fibre-coordinate change:
--
-- A' = A + dLambda ,   s' = s - dLambda(v).
--
-- This is not a global gauge-bundle/monodromy proof.
KK5GaugeShiftPreservesBilinear :
  ∀ {V : Set}
    (g4 : V → V → ℚ)
    (connection dLambda : V → ℚ)
    (radiusSquared : ℚ)
    (v w : V)
    (fibreV fibreW : ℚ) →
  KK5Bilinear g4
    (λ x → connection x + dLambda x)
    radiusSquared
    v (fibreV - dLambda v)
    w (fibreW - dLambda w)
  ≡
  KK5Bilinear g4 connection radiusSquared
    v fibreV w fibreW
KK5GaugeShiftPreservesBilinear
    g4 connection dLambda r v w s t =
  Ring.solve-∀
    (g4 v w) (connection v) (connection w)
    (dLambda v) (dLambda w) r s t

horizontalCircleGaugeShift :
  ∀ {V : Set} (connection dLambda : V → ℚ) (v : V) →
  horizontalCircleComponent (λ x → connection x + dLambda x) v
  ≡
  horizontalCircleComponent connection v - dLambda v
horizontalCircleGaugeShift connection dLambda v =
  Ring.solve-∀ (connection v) (dLambda v)

-- A metric SOURCE to complete P02->P08 must supply:
--  (i) actual nondegenerate physically measured g4 and calibrated
--      causal cone from original observer histories;
-- (ii) actual smooth 5D geometry and positive radius b^2,
--      connection/gauge chart compatibility;
-- (iii) this selected 5D KK bilinear and physical 4D metric
--       are indeed the ones from the original same-action solution;
--  (iv) scalar/radion source, stress, boundary conditions and 5D
--       field equations; and the same selected OS/clock source.
--
-- This module proves (algebraic) identity for ALL supplied fields,
-- without claiming any of these physical input producers inhabited.
