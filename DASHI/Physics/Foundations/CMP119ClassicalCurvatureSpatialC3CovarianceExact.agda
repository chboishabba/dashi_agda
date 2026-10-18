{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119ClassicalCurvatureSpatialC3CovarianceExact where

------------------------------------------------------------------------
-- CLASSICAL YM CURVATURE/STRESS REALISATION OF THE SPATIAL C3 ACTION
--
-- The Q1 present-cut lane needs one tangent->curve source realisation for the
-- full generated effective action.  That source payment is genuine, but it is
-- stronger than what is required to see the physical spatial C3 action in the
-- classical Yang--Mills stress tensor.
--
-- The repository already owns the exact d=4 six-curvature carrier and its ten
-- metric variations / stress insertions.  Here we act on the curvature 2-form
-- under the spatial cycle
--
--      1 -> 2 -> 3 -> 1,     0 fixed.
--
-- With stored components ordered as
--
--   (F01,F02,F03,F12,F13,F23),
--
-- active tensor transport gives
--
--   (F03,F01,F02,-F13,-F23,F12).
--
-- The signs are the antisymmetry of the two-form, not an additional physical
-- convention.  We prove that the existing ten metric variations and classical
-- stress insertions transform under exactly the SAME `spatialXYZComponent`
-- action already used by the R144/B4 stress lane.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119ClassicalCurvatureTenMetricVariationExact as Metric
import DASHI.Physics.Foundations.CMP119ClassicalCurvatureStressInsertionExact as Stress
import DASHI.Physics.Foundations.BalabanR144SpatialC3StressRestrictionExact as Spatial
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlScalarExact as Curl

spatialC3Curvature : Metric.CurvatureSix → Metric.CurvatureSix
spatialC3Curvature curvature = record
  { Metric.CurvatureSix.f01 = Metric.f03 curvature
  ; Metric.CurvatureSix.f02 = Metric.f01 curvature
  ; Metric.CurvatureSix.f03 = Metric.f02 curvature
  ; Metric.CurvatureSix.f12 = Curl.negV (Metric.f13 curvature)
  ; Metric.CurvatureSix.f13 = Curl.negV (Metric.f23 curvature)
  ; Metric.CurvatureSix.f23 = Metric.f12 curvature
  }

energyNeg : ∀ value →
  Metric.energy (Curl.negV value) ≡ Metric.energy value
energyNeg (Curl.vec3 x y z) =
  ℚRing.solve-∀ x y z

vectorDotCommutative : ∀ left right →
  Curl.vectorDot left right ≡ Curl.vectorDot right left
vectorDotCommutative
  (Curl.vec3 ax ay az) (Curl.vec3 bx by bz) =
  ℚRing.solve-∀ ax ay az bx by bz

------------------------------------------------------------------------
-- The classical action variation is an honest rank-two tensor under this C3.
------------------------------------------------------------------------

spatialC3MetricVariationCovariant :
  ∀ curvature component →
  Metric.actionVariation
    (spatialC3Curvature curvature)
    (Spatial.spatialXYZComponent component)
  ≡ Metric.actionVariation curvature component

spatialC3MetricVariationCovariant curvature K.component00
  rewrite energyNeg (Metric.f13 curvature)
        | energyNeg (Metric.f23 curvature) =
  ℚRing.solve-∀
    (Metric.energy (Metric.f01 curvature))
    (Metric.energy (Metric.f02 curvature))
    (Metric.energy (Metric.f03 curvature))
    (Metric.energy (Metric.f12 curvature))
    (Metric.energy (Metric.f13 curvature))
    (Metric.energy (Metric.f23 curvature))

spatialC3MetricVariationCovariant curvature K.component11
  rewrite energyNeg (Metric.f13 curvature)
        | energyNeg (Metric.f23 curvature) =
  ℚRing.solve-∀
    (Metric.energy (Metric.f01 curvature))
    (Metric.energy (Metric.f02 curvature))
    (Metric.energy (Metric.f03 curvature))
    (Metric.energy (Metric.f12 curvature))
    (Metric.energy (Metric.f13 curvature))
    (Metric.energy (Metric.f23 curvature))

spatialC3MetricVariationCovariant curvature K.component22
  rewrite energyNeg (Metric.f13 curvature)
        | energyNeg (Metric.f23 curvature) =
  ℚRing.solve-∀
    (Metric.energy (Metric.f01 curvature))
    (Metric.energy (Metric.f02 curvature))
    (Metric.energy (Metric.f03 curvature))
    (Metric.energy (Metric.f12 curvature))
    (Metric.energy (Metric.f13 curvature))
    (Metric.energy (Metric.f23 curvature))

spatialC3MetricVariationCovariant curvature K.component33
  rewrite energyNeg (Metric.f13 curvature)
        | energyNeg (Metric.f23 curvature) =
  ℚRing.solve-∀
    (Metric.energy (Metric.f01 curvature))
    (Metric.energy (Metric.f02 curvature))
    (Metric.energy (Metric.f03 curvature))
    (Metric.energy (Metric.f12 curvature))
    (Metric.energy (Metric.f13 curvature))
    (Metric.energy (Metric.f23 curvature))

spatialC3MetricVariationCovariant curvature K.component01
  rewrite Curl.vectorDotNegRight
            (Metric.f03 curvature) (Metric.f13 curvature) =
  ℚRing.solve-∀
    (Curl.vectorDot (Metric.f02 curvature) (Metric.f12 curvature))
    (Curl.vectorDot (Metric.f03 curvature) (Metric.f13 curvature))

spatialC3MetricVariationCovariant curvature K.component02
  rewrite Curl.vectorDotNegRight
            (Metric.f03 curvature) (Metric.f23 curvature) =
  ℚRing.solve-∀
    (Curl.vectorDot (Metric.f01 curvature) (Metric.f12 curvature))
    (Curl.vectorDot (Metric.f03 curvature) (Metric.f23 curvature))

spatialC3MetricVariationCovariant curvature K.component03
  rewrite Curl.vectorDotNegRight
            (Metric.f01 curvature) (Metric.f13 curvature)
        | Curl.vectorDotNegRight
            (Metric.f02 curvature) (Metric.f23 curvature) =
  ℚRing.solve-∀
    (Curl.vectorDot (Metric.f01 curvature) (Metric.f13 curvature))
    (Curl.vectorDot (Metric.f02 curvature) (Metric.f23 curvature))

spatialC3MetricVariationCovariant curvature K.component12
  rewrite Curl.vectorDotNegBoth
            (Metric.f13 curvature) (Metric.f23 curvature) =
  ℚRing.solve-∀
    (Curl.vectorDot (Metric.f01 curvature) (Metric.f02 curvature))
    (Curl.vectorDot (Metric.f13 curvature) (Metric.f23 curvature))

spatialC3MetricVariationCovariant curvature K.component23
  rewrite Curl.vectorDotNegLeft
            (Metric.f13 curvature) (Metric.f12 curvature)
        | vectorDotCommutative
            (Metric.f03 curvature) (Metric.f02 curvature)
        | vectorDotCommutative
            (Metric.f13 curvature) (Metric.f12 curvature) =
  ℚRing.solve-∀
    (Curl.vectorDot (Metric.f02 curvature) (Metric.f03 curvature))
    (Curl.vectorDot (Metric.f12 curvature) (Metric.f13 curvature))

spatialC3MetricVariationCovariant curvature K.component13
  rewrite Curl.vectorDotNegLeft
            (Metric.f23 curvature) (Metric.f12 curvature)
        | vectorDotCommutative
            (Metric.f03 curvature) (Metric.f01 curvature)
        | vectorDotCommutative
            (Metric.f23 curvature) (Metric.f12 curvature) =
  ℚRing.solve-∀
    (Curl.vectorDot (Metric.f01 curvature) (Metric.f03 curvature))
    (Curl.vectorDot (Metric.f12 curvature) (Metric.f23 curvature))

------------------------------------------------------------------------
-- The existing classical stress normalization preserves that covariance.
------------------------------------------------------------------------

spatialC3StressCovariant :
  ∀ curvature component →
  Stress.stressInsertion
    (spatialC3Curvature curvature)
    (Spatial.spatialXYZComponent component)
  ≡ Stress.stressInsertion curvature component
spatialC3StressCovariant curvature K.component00 =
  cong (λ value → - (Stress.two * value))
    (spatialC3MetricVariationCovariant curvature K.component00)
spatialC3StressCovariant curvature K.component01 =
  cong (λ value → - value)
    (spatialC3MetricVariationCovariant curvature K.component01)
spatialC3StressCovariant curvature K.component02 =
  cong (λ value → - value)
    (spatialC3MetricVariationCovariant curvature K.component02)
spatialC3StressCovariant curvature K.component03 =
  cong (λ value → - value)
    (spatialC3MetricVariationCovariant curvature K.component03)
spatialC3StressCovariant curvature K.component11 =
  cong (λ value → - (Stress.two * value))
    (spatialC3MetricVariationCovariant curvature K.component11)
spatialC3StressCovariant curvature K.component12 =
  cong (λ value → - value)
    (spatialC3MetricVariationCovariant curvature K.component12)
spatialC3StressCovariant curvature K.component13 =
  cong (λ value → - value)
    (spatialC3MetricVariationCovariant curvature K.component13)
spatialC3StressCovariant curvature K.component22 =
  cong (λ value → - (Stress.two * value))
    (spatialC3MetricVariationCovariant curvature K.component22)
spatialC3StressCovariant curvature K.component23 =
  cong (λ value → - value)
    (spatialC3MetricVariationCovariant curvature K.component23)
spatialC3StressCovariant curvature K.component33 =
  cong (λ value → - (Stress.two * value))
    (spatialC3MetricVariationCovariant curvature K.component33)

------------------------------------------------------------------------
-- Frontier accounting.
------------------------------------------------------------------------

classicalCurvatureSpatialC3Recovered : Bool
classicalCurvatureSpatialC3Recovered = true

classicalStressSpatialC3Recovered : Bool
classicalStressSpatialC3Recovered = true

classicalStressUsesSameR144SpatialTensorAction : Bool
classicalStressUsesSameR144SpatialTensorAction = true

-- This pays an explicit continuous/field-strength realisation of the spatial
-- C3 tensor law.  It does NOT identify the whole CMP109/116 generated effective
-- action with the classical curvature action, so the generated-action Q1
-- tangent->curve source semantics remains a separate source payment.
classicalCurvatureC3ClosesFullGeneratedActionQ1 : Bool
classicalCurvatureC3ClosesFullGeneratedActionQ1 = false
