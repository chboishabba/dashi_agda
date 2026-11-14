module DASHI.Physics.YangMills.BalabanCMP109116BishopRealSetoidInstantiationExact where

------------------------------------------------------------------------
-- CONSTRUCTED BISHOP REALS IN PLACE OF THE POSTULATED LEGACY REAL.
--
-- Real.ℝ / Real._≃_ are the vendor's actual constructive real model.
-- There is NO postulate in this module and NO import of RealAnalysisAxioms.
-- Existing source-owned Bishop arithmetic/order is used directly.
--
-- This instantiates the postulate-free CMP109/CMP116 algebraic core; it
-- does NOT silently identify Bishop setoid equality with propositional
-- equality or prove that the original finite Wilson/FP/Haar source uses
-- this backend. That final migration requires the physical model and
-- all equality-sensitive source signatures to be transported.
------------------------------------------------------------------------

import Real as Bishop
import RealProperties as BishopProperties

import DASHI.Physics.YangMills.BalabanCMP109116ConstructiveScalarCoreExact as Core

BishopDifferentiatedAction : (Background Tangent : Set) → Set₁
BishopDifferentiatedAction Background Tangent =
  Core.OnePhysicalDifferentiatedAction Bishop.ℝ Background Tangent

bishopCMP109CMP116Agreement :
  ∀ {Background Tangent}
    (action : BishopDifferentiatedAction Background Tangent)
    background u v →
  Bishop._≃_
    (Core.cmp109Polarization action background u v)
    (Core.cmp116PhysicalMarkedHessian action background u v)
bishopCMP109CMP116Agreement action background u v =
  BishopProperties.≃-refl

record BishopSameSourceHeatExpectation
    {Background Tangent : Set}
    (action : BishopDifferentiatedAction Background Tangent)
    (Time : Set) : Set₁ where
  field
    firstVariation :
      (Background → Bishop.ℝ) →
      Background → Tangent → Bishop.ℝ

    expectation :
      Time → Background → (Background → Bishop.ℝ) → Bishop.ℝ

  asPostulateFreeAlgebra :
    Core.SameSourceHeatDoobAlgebra action Time
  asPostulateFreeAlgebra = record
    { Core.SameSourceHeatDoobAlgebra.subtract = Bishop._-_
    ; Core.SameSourceHeatDoobAlgebra.multiply = Bishop._*_
    ; Core.SameSourceHeatDoobAlgebra.firstVariation = firstVariation
    ; Core.SameSourceHeatDoobAlgebra.expectation = expectation
    }

open BishopSameSourceHeatExpectation public

-- The remaining REAL physical obligation is to derive the finite-cutoff
-- normalized Haar/heat expectation above from the SAME Wilson density
-- with analytic derivative, source equality and positivity proofs.
