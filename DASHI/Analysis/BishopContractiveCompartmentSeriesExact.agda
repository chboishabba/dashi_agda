module DASHI.Analysis.BishopContractiveCompartmentSeriesExact where

------------------------------------------------------------------------
-- BISHOP POLYNOMIAL-GEOMETRIC COMPARTMENT MAJORANTS
--
-- SOURCE / ATTRIBUTION
--
-- The constructive convergence theorem is reused directly from
-- BishopPolynomialGeometricSeriesConvergenceExact, itself built from the
-- pinned Murray/Bishop constructive-real library.
--
-- DASHI CONTRIBUTION
--
-- This owner removes the Eisenstein/Moonshine vocabulary and exposes exactly
-- the reusable compartment-kernel shape:
--
--   scale * (n+1)^degree * ratio^(n+1),   0 <= ratio < 1.
--
-- It proves constructive convergence and absolute convergence for every fixed
-- natural degree.  An ecological, chemical, biological or other consumer must
-- still prove that its actual contribution is bounded by such a majorant.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Analysis.BishopPolynomialGeometricSeriesConvergenceExact as PolyGeo

record BishopPolynomialGeometricCompartment : Set where
  field
    scale : BishopReal.ℝ
    ratio : BishopReal.ℝ
    degree : Nat

    ratioNonnegative :
      BishopReal._≤_ BishopReal.0ℝ ratio

    ratioBelowOne :
      BishopReal._<_ ratio BishopReal.1ℝ

    scaleNonnegative :
      BishopReal.NonNegative scale

open BishopPolynomialGeometricCompartment public

compartmentMajorantTerm :
  BishopPolynomialGeometricCompartment →
  Nat →
  BishopReal.ℝ
compartmentMajorantTerm problem =
  PolyGeo.shiftedScaledPolynomialGeometricTerm
    (scale problem)
    (ratio problem)
    (degree problem)

compartmentMajorantConvergent :
  (problem : BishopPolynomialGeometricCompartment) →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf
      (compartmentMajorantTerm problem))
compartmentMajorantConvergent problem =
  PolyGeo.shiftedScaledPolynomialGeometricSeriesConvergent
    (ratio problem)
    (scale problem)
    (degree problem)
    (ratioNonnegative problem)
    (ratioBelowOne problem)
    (scaleNonnegative problem)

compartmentMajorantAbsolutelyConvergent :
  (problem : BishopPolynomialGeometricCompartment) →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (compartmentMajorantTerm problem)
compartmentMajorantAbsolutelyConvergent problem =
  PolyGeo.shiftedScaledPolynomialGeometricSeriesAbsolutelyConvergent
    (ratio problem)
    (scale problem)
    (degree problem)
    (ratioNonnegative problem)
    (ratioBelowOne problem)
    (scaleNonnegative problem)
