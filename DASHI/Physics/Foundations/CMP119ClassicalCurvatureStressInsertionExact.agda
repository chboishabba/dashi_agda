{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119ClassicalCurvatureStressInsertionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; -_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119ClassicalCurvatureTenMetricVariationExact as Metric

------------------------------------------------------------------------
-- CLASSICAL LOCAL STRESS INSERTION FROM METRIC VARIATION
--
-- For diagonal coordinates:
--   δS = -(1/2) T_aa δg_aa  =>  T_aa = -2 DS_aa.
--
-- For one independent symmetric off-diagonal coordinate h_ab (a<b), both
-- matrix entries g_ab and g_ba vary, hence
--   δS = - T_ab h_ab         =>  T_ab = - DS_ab.
--
-- This normalization exactly reproduces the Euclidean YM tensor
--   T_ab = F_{aρ}.F_{bρ} - (1/4) δ_ab F^2.
------------------------------------------------------------------------

two : ℚ
two = + 2 / 1

stressInsertion :
  Metric.CurvatureSix → K.SymmetricTensorComponent4 → ℚ
stressInsertion curvature K.component00 =
  - (two * Metric.actionVariation curvature K.component00)
stressInsertion curvature K.component01 =
  - Metric.actionVariation curvature K.component01
stressInsertion curvature K.component02 =
  - Metric.actionVariation curvature K.component02
stressInsertion curvature K.component03 =
  - Metric.actionVariation curvature K.component03
stressInsertion curvature K.component11 =
  - (two * Metric.actionVariation curvature K.component11)
stressInsertion curvature K.component12 =
  - Metric.actionVariation curvature K.component12
stressInsertion curvature K.component13 =
  - Metric.actionVariation curvature K.component13
stressInsertion curvature K.component22 =
  - (two * Metric.actionVariation curvature K.component22)
stressInsertion curvature K.component23 =
  - Metric.actionVariation curvature K.component23
stressInsertion curvature K.component33 =
  - (two * Metric.actionVariation curvature K.component33)

stress00Expanded : ∀ curvature →
  stressInsertion curvature K.component00
  ≡ Metric.energy (Metric.f01 curvature)
   + Metric.energy (Metric.f02 curvature)
   + Metric.energy (Metric.f03 curvature)
   - Metric.energy (Metric.f12 curvature)
   - Metric.energy (Metric.f13 curvature)
   - Metric.energy (Metric.f23 curvature)
stress00Expanded curvature =
  ℚRing.solve-∀
    (Metric.energy (Metric.f01 curvature))
    (Metric.energy (Metric.f02 curvature))
    (Metric.energy (Metric.f03 curvature))
    (Metric.energy (Metric.f12 curvature))
    (Metric.energy (Metric.f13 curvature))
    (Metric.energy (Metric.f23 curvature))

stress11Expanded : ∀ curvature →
  stressInsertion curvature K.component11
  ≡ Metric.energy (Metric.f01 curvature)
   - Metric.energy (Metric.f02 curvature)
   - Metric.energy (Metric.f03 curvature)
   + Metric.energy (Metric.f12 curvature)
   + Metric.energy (Metric.f13 curvature)
   - Metric.energy (Metric.f23 curvature)
stress11Expanded curvature =
  ℚRing.solve-∀
    (Metric.energy (Metric.f01 curvature))
    (Metric.energy (Metric.f02 curvature))
    (Metric.energy (Metric.f03 curvature))
    (Metric.energy (Metric.f12 curvature))
    (Metric.energy (Metric.f13 curvature))
    (Metric.energy (Metric.f23 curvature))

stress22Expanded : ∀ curvature →
  stressInsertion curvature K.component22
  ≡ - Metric.energy (Metric.f01 curvature)
   + Metric.energy (Metric.f02 curvature)
   - Metric.energy (Metric.f03 curvature)
   + Metric.energy (Metric.f12 curvature)
   - Metric.energy (Metric.f13 curvature)
   + Metric.energy (Metric.f23 curvature)
stress22Expanded curvature =
  ℚRing.solve-∀
    (Metric.energy (Metric.f01 curvature))
    (Metric.energy (Metric.f02 curvature))
    (Metric.energy (Metric.f03 curvature))
    (Metric.energy (Metric.f12 curvature))
    (Metric.energy (Metric.f13 curvature))
    (Metric.energy (Metric.f23 curvature))

stress33Expanded : ∀ curvature →
  stressInsertion curvature K.component33
  ≡ - Metric.energy (Metric.f01 curvature)
   - Metric.energy (Metric.f02 curvature)
   + Metric.energy (Metric.f03 curvature)
   - Metric.energy (Metric.f12 curvature)
   + Metric.energy (Metric.f13 curvature)
   + Metric.energy (Metric.f23 curvature)
stress33Expanded curvature =
  ℚRing.solve-∀
    (Metric.energy (Metric.f01 curvature))
    (Metric.energy (Metric.f02 curvature))
    (Metric.energy (Metric.f03 curvature))
    (Metric.energy (Metric.f12 curvature))
    (Metric.energy (Metric.f13 curvature))
    (Metric.energy (Metric.f23 curvature))

stress01Expanded : ∀ curvature →
  stressInsertion curvature K.component01 ≡ Metric.k01 curvature
stress01Expanded curvature = refl

stress02Expanded : ∀ curvature →
  stressInsertion curvature K.component02 ≡ Metric.k02 curvature
stress02Expanded curvature = refl

stress03Expanded : ∀ curvature →
  stressInsertion curvature K.component03 ≡ Metric.k03 curvature
stress03Expanded curvature = refl

stress12Expanded : ∀ curvature →
  stressInsertion curvature K.component12 ≡ Metric.k12 curvature
stress12Expanded curvature = refl

stress13Expanded : ∀ curvature →
  stressInsertion curvature K.component13 ≡ Metric.k13 curvature
stress13Expanded curvature = refl

stress23Expanded : ∀ curvature →
  stressInsertion curvature K.component23 ≡ Metric.k23 curvature
stress23Expanded curvature = refl

classicalStressTrace :
  Metric.CurvatureSix → ℚ
classicalStressTrace curvature =
  stressInsertion curvature K.component00
  + stressInsertion curvature K.component11
  + stressInsertion curvature K.component22
  + stressInsertion curvature K.component33

classicalStressTraceIsZero :
  ∀ curvature → classicalStressTrace curvature ≡ 0ℚ
classicalStressTraceIsZero curvature
  rewrite Metric.diagonalTraceZero curvature =
  ℚRing.solve []

record FiniteClassicalStressInsertionFamily (Configuration : Set) : Set₁ where
  field
    curvature :
      Metric.FiniteCurvatureSixFamily Configuration

open FiniteClassicalStressInsertionFamily public

stressInsertionAt :
  ∀ {Configuration} →
  FiniteClassicalStressInsertionFamily Configuration →
  K.SymmetricTensorComponent4 →
  Configuration → ℚ
stressInsertionAt family component configuration =
  stressInsertion
    (Metric.curvatureAt (curvature family) configuration)
    component

pointwiseStressTraceZero :
  ∀ {Configuration}
    (family : FiniteClassicalStressInsertionFamily Configuration)
    configuration →
  stressInsertionAt family K.component00 configuration
  + stressInsertionAt family K.component11 configuration
  + stressInsertionAt family K.component22 configuration
  + stressInsertionAt family K.component33 configuration
  ≡ 0ℚ
pointwiseStressTraceZero family configuration =
  classicalStressTraceIsZero
    (Metric.curvatureAt (curvature family) configuration)
