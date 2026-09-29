{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119FlatSide4CurvatureStressExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)

import DASHI.Physics.Foundations.CMP119ClassicalCurvatureTenMetricVariationExact as Metric
import DASHI.Physics.Foundations.CMP119ClassicalCurvatureStressInsertionExact as Stress
import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatWilsonCurlIdentificationExact as Flat
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Wilson
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge

------------------------------------------------------------------------
-- EXACT SIDE-4 / IDENTITY-BACKGROUND CURVATURE REALIZATION
--
-- Each local curvature component is the three Lie-coordinate periodic curl
-- already used by the literal flat Wilson-Hessian theorem.
------------------------------------------------------------------------

localCurvatureVector :
  Physical.PhysicalSU2BondField4 →
  Hodge.Axis4 → Hodge.Axis4 → Hodge.Site4 →
  Wilson.RationalVector3
localCurvatureVector field left right site =
  Wilson.vec3
    (Flat.plaquetteCurlCoordinate
      field Physical.coordinateX left right site)
    (Flat.plaquetteCurlCoordinate
      field Physical.coordinateY left right site)
    (Flat.plaquetteCurlCoordinate
      field Physical.coordinateZ left right site)

localCurvatureSix :
  Physical.PhysicalSU2BondField4 →
  Hodge.Site4 →
  Metric.CurvatureSix
localCurvatureSix field site = record
  { Metric.CurvatureSix.f01 =
      localCurvatureVector field Hodge.axis0 Hodge.axis1 site
  ; Metric.CurvatureSix.f02 =
      localCurvatureVector field Hodge.axis0 Hodge.axis2 site
  ; Metric.CurvatureSix.f03 =
      localCurvatureVector field Hodge.axis0 Hodge.axis3 site
  ; Metric.CurvatureSix.f12 =
      localCurvatureVector field Hodge.axis1 Hodge.axis2 site
  ; Metric.CurvatureSix.f13 =
      localCurvatureVector field Hodge.axis1 Hodge.axis3 site
  ; Metric.CurvatureSix.f23 =
      localCurvatureVector field Hodge.axis2 Hodge.axis3 site
  }

localStressInsertion :
  Physical.PhysicalSU2BondField4 →
  Hodge.Site4 →
  K.SymmetricTensorComponent4 →
  ℚ
localStressInsertion field site component =
  Stress.stressInsertion (localCurvatureSix field site) component

localStressTrace :
  Physical.PhysicalSU2BondField4 →
  Hodge.Site4 → ℚ
localStressTrace field site =
  localStressInsertion field site K.component00
  + localStressInsertion field site K.component11
  + localStressInsertion field site K.component22
  + localStressInsertion field site K.component33

localStressTraceIsZero :
  ∀ field site → localStressTrace field site ≡ 0ℚ
localStressTraceIsZero field site =
  Stress.classicalStressTraceIsZero (localCurvatureSix field site)

localActionVariation :
  Physical.PhysicalSU2BondField4 →
  Hodge.Site4 →
  K.SymmetricTensorComponent4 →
  ℚ
localActionVariation field site component =
  Metric.actionVariation (localCurvatureSix field site) component

localDiagonalActionTraceIsZero :
  ∀ field site →
  localActionVariation field site K.component00
  + localActionVariation field site K.component11
  + localActionVariation field site K.component22
  + localActionVariation field site K.component33
  ≡ 0ℚ
localDiagonalActionTraceIsZero field site =
  Metric.diagonalTraceZero (localCurvatureSix field site)
