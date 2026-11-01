{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.EinsteinFiniteToPhysicalCalibrationCompilerExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Closure.DiscreteWarpedEinsteinMatterModel as Model
import DASHI.Physics.Closure.EinsteinEquationBidiResidualExact as Finite

------------------------------------------------------------------------
-- NORMALIZED FINITE EINSTEIN LAW -> PHYSICAL COUPLING LAW
--
-- The finite fixture proves G_f = T_f at normalized kappa=1.  A physical
-- unit/calibration map need not identify "1" with 8*pi*G/c^4.  Instead it
-- supplies two scale maps and the one required scale-commutation theorem:
--
--   scale_G(c) = kappa_phys (scale_T(c)).
--
-- Then the finite same-component equality transports mechanically to
--
--   scale_G(G_f) = kappa_phys(scale_T(T_f)).
--
-- This is the exact algebraic bridge between normalized and physical coupling.
-- Analytic continuum convergence and accepted measured-G authority remain
-- separate obligations.
------------------------------------------------------------------------

record EinsteinFiniteToPhysicalCalibration : Set₁ where
  field
    PhysicalCoefficient : Set

    curvatureToPhysical :
      Model.SourceCoefficient → PhysicalCoefficient

    stressToPhysical :
      Model.SourceCoefficient → PhysicalCoefficient

    applyPhysicalEinsteinCoupling :
      PhysicalCoefficient → PhysicalCoefficient

    normalizedScaleCommutesWithPhysicalCoupling :
      ∀ coefficient →
      curvatureToPhysical coefficient
      ≡ applyPhysicalEinsteinCoupling
          (stressToPhysical coefficient)

    acceptedMeasuredGCoupling : Bool
    acceptedMeasuredGCouplingIsFalse :
      acceptedMeasuredGCoupling ≡ false

    analyticContinuumRealization : Bool
    analyticContinuumRealizationIsFalse :
      analyticContinuumRealization ≡ false

open EinsteinFiniteToPhysicalCalibration public

finiteEquationTransportsToPhysicalEquation :
  (calibration : EinsteinFiniteToPhysicalCalibration) →
  (a b : Flat.Axis4) →
  curvatureToPhysical calibration
      (Model.computedEinsteinTensor a b)
  ≡
  applyPhysicalEinsteinCoupling calibration
    (stressToPhysical calibration
      (Model.computedMatterStress a b))
finiteEquationTransportsToPhysicalEquation calibration a b =
  trans
    (normalizedScaleCommutesWithPhysicalCoupling calibration
      (Model.computedEinsteinTensor a b))
    (cong
      (λ coefficient →
        applyPhysicalEinsteinCoupling calibration
          (stressToPhysical calibration coefficient))
      (Model.computedEinsteinEqualsMatterStress a b))

record PhysicalEinsteinTransportBoundary : Set where
  constructor physicalEinsteinTransportBoundary
  field
    normalizedFiniteEquationNeedsReproofAfterCalibration : Bool
    normalizedFiniteEquationNeedsReproofAfterCalibrationIsFalse :
      normalizedFiniteEquationNeedsReproofAfterCalibration ≡ false

    scaleCommutationCanBeInferredFromKappaOne : Bool
    scaleCommutationCanBeInferredFromKappaOneIsFalse :
      scaleCommutationCanBeInferredFromKappaOne ≡ false

    continuumConvergenceCanBeInferredFromScaleCommutation : Bool
    continuumConvergenceCanBeInferredFromScaleCommutationIsFalse :
      continuumConvergenceCanBeInferredFromScaleCommutation ≡ false

canonicalPhysicalEinsteinTransportBoundary :
  PhysicalEinsteinTransportBoundary
canonicalPhysicalEinsteinTransportBoundary =
  physicalEinsteinTransportBoundary false refl false refl false refl
