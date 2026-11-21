{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSFVKKFourMetricVerticalProbeFullReconstructionExact where

------------------------------------------------------------------------
-- KK08 / KK10 / BIDI03: SOURCE KK5 FULL METRIC TOMOGRAPHY.
--
-- The earlier original KK inverse no-go proves g4 alone loses the
-- fibre radius and gauge connection. This is the complementary
-- sufficiency theorem: the same original horizontal four-bilinear,
-- the selected fifth-circle radius and the measured mixed connection
-- on each tangent vector uniquely determine the WHOLE 5D KK
-- bilinear for all tangent/fibre test pairs.
--
-- No separate chosen five-metric or equality of full metrics is an
-- input. This proves a minimal algebraic 5D observable dictionary.
-- The physical microscope must still actually measure these probes,
-- show smooth source geometry, and construct a 5D Einstein solution.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using
  (cong; trans; sym)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)

import DASHI.Physics.Foundations.TSFVKKSelectedHorizontalMetricSchurExact
  as KK
import DASHI.Physics.Foundations.TSFVKKHorizontalReductionNoninjectiveBidiExact
  as Inverse

-- Every fibre/tangent pair, not just horizontal pairs. The proof
-- normalizes all source measurements before evaluating the single
-- ORIGINAL KK5Bilinear constructor.
originalKKFullFiveMetricRecoveredFromThreeProbeFamilies :
  ∀ {V : Set}
  (measuredFourA measuredFourB : V → V → ℚ)
  (connectionA connectionB : V → ℚ)
  (radiusA radiusB : ℚ) →
  (fourMeasurementEqual :
    ∀ v w → measuredFourA v w ≡ measuredFourB v w) →
  (connectionMeasurementEqual :
    ∀ v → connectionA v ≡ connectionB v) →
  (radiusMeasurementEqual : radiusA ≡ radiusB) →
  ∀ v fibreV w fibreW →
  KK.KK5Bilinear measuredFourA connectionA radiusA
    v fibreV w fibreW
  ≡
  KK.KK5Bilinear measuredFourB connectionB radiusB
    v fibreV w fibreW
originalKKFullFiveMetricRecoveredFromThreeProbeFamilies
    measuredFourA measuredFourB
    connectionA connectionB radiusA radiusB
    fourMeasurementEqual connectionMeasurementEqual
    radiusMeasurementEqual v fibreV w fibreW
  rewrite fourMeasurementEqual v w
        | connectionMeasurementEqual v
        | connectionMeasurementEqual w
        | radiusMeasurementEqual = refl

-- The selected original radius probe (with the SAME connection)
-- is exact on the genuine KK5 bilinear: no new postulated radius
-- observation or second five-metric declaration is introduced.
originalKKVerticalProbeReadsSelectedRadion :
  ∀ {V : Set} →
  (measuredFour : V → V → ℚ)
  (connection : V → ℚ)
  (radiusSquared : ℚ)
  (v w : V) →
  KK.KK5Bilinear measuredFour connection radiusSquared
    v (1ℚ - connection v)
    w (1ℚ - connection w)
  - measuredFour v w
  ≡ radiusSquared
originalKKVerticalProbeReadsSelectedRadion =
  Inverse.originalFiveMetricVerticalProbeReadsFibreRadius

-- At unit fibre normalization, a DIFFERENCE of true 5D mixed
-- measurements reads the selected source connection A(v).
originalKKUnitFibreMixedProbeReadsConnection :
  ∀ {V : Set} →
  (measuredFour : V → V → ℚ)
  (connection : V → ℚ)
  (v w : V) →
  (KK.KK5Bilinear measuredFour connection 1ℚ
    v 0ℚ w 1ℚ)
  -
  (KK.KK5Bilinear measuredFour connection 1ℚ
    v 0ℚ w 0ℚ)
  ≡ connection v
originalKKUnitFibreMixedProbeReadsConnection =
  Inverse.originalFiveMetricMixedVerticalDifferenceReadsConnection

-- Any actual physical metrology asserting full 5D identity must
-- derive the base, circle-radius and mixed probes on one original
-- state, in one physical gauge/bundle trivialization. This file
-- proves that this finite set of TEST TYPES is sufficient, not that
-- TSVF/OS supplies the physical results or actual 5D curvature.
