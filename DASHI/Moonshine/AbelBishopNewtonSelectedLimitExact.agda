module DASHI.Moonshine.AbelBishopNewtonSelectedLimitExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP NEWTON ITERATES -> CONCRETE COMPLETED FIXED POINT.
--
-- The selected literal Newton stream lives in
-- AbelBishopNewtonSelectedOperatorExact, on the SAME original
-- Bishop expC/reciprocal carrier.
--
-- Only source analytic inputs:
-- (1) pointwise 1/15000*(1/200)^n coordinate bounds for the actual
--     Newton step difference, not a surrogate geometric sequence;
-- (2) the actual Newton endomap's continuity along the SAME stream.
--
-- All convergence, completion, shift, uniqueness and setoid fixed
-- equality are constructed from prior Bishop sources. This does
-- NOT assert that either analytic input has been proved.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_,_)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Native
import DASHI.Foundations.BishopPolynomialGeometricDominationConvergenceExact as Geometric
import DASHI.Moonshine.AbelBishopKoenigsSelectedRationalConstantsExact as Constants
import DASHI.Moonshine.AbelBishopNewtonSelectedOperatorExact as Newton
import DASHI.Moonshine.AbelBishopKoenigsFiniteTelescopingExact as Telescope
import DASHI.Moonshine.AbelBishopKoenigsGeometricAbsoluteExact as Bounds
import DASHI.Moonshine.AbelBishopInverseKoenigsGeometricOrbitExact as Limit
import DASHI.Moonshine.AbelBishopInverseKoenigsShiftConvergenceExact as Shift
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion

record OriginalBishopNewtonSelectedStepBounds
    (T : Cartesian.BishopSetoidComplexTranscendentals)
    (nz : Reciprocal.BishopComplexNonzero
      (Newton.originalBishopNewtonDenominator T)) : Set₁ where
  field
    realStepBound :
      ∀ n →
      BishopReal._≤_
        (BishopReal.∣ Complex.re
          (Telescope.originalBishopComplexStepDifference
            (Newton.originalBishopNewtonOrbit T nz) n) ∣)
        (Geometric.scaledGeometricTerm
          Constants.bishopSelectedNewtonIncrementConstant
          Constants.bishopSelectedNewtonRatio n)

    imagStepBound :
      ∀ n →
      BishopReal._≤_
        (BishopReal.∣ Complex.im
          (Telescope.originalBishopComplexStepDifference
            (Newton.originalBishopNewtonOrbit T nz) n) ∣)
        (Geometric.scaledGeometricTerm
          Constants.bishopSelectedNewtonIncrementConstant
          Constants.bishopSelectedNewtonRatio n)
open OriginalBishopNewtonSelectedStepBounds public

originalSelectedNewtonBoundsBuildBishopConvergenceInputs :
  ∀ T nz →
  OriginalBishopNewtonSelectedStepBounds T nz →
  Bounds.OriginalBishopGeometricComponentBounds
    (Telescope.originalBishopComplexStepDifference
      (Newton.originalBishopNewtonOrbit T nz))
    Constants.bishopSelectedNewtonIncrementConstant
    Constants.bishopSelectedNewtonRatio
originalSelectedNewtonBoundsBuildBishopConvergenceInputs T nz input =
  record
    { Bounds.geometricInputs =
        Constants.bishopSelectedNewtonGeometricInputs
    ; Bounds.realComponentBound = realStepBound input
    ; Bounds.imaginaryComponentBound = imagStepBound input
    }

originalBishopSelectedNewtonLimit :
  ∀ T nz →
  OriginalBishopNewtonSelectedStepBounds T nz →
  Complex.BishopComplex
originalBishopSelectedNewtonLimit T nz input =
  Limit.originalBishopGeometricOrbitLimit
    (Newton.originalBishopNewtonOrbit T nz)
    Constants.bishopSelectedNewtonIncrementConstant
    Constants.bishopSelectedNewtonRatio
    (originalSelectedNewtonBoundsBuildBishopConvergenceInputs
      T nz input)

originalBishopSelectedNewtonConverges :
  ∀ T nz →
  (input : OriginalBishopNewtonSelectedStepBounds T nz) →
  Completion.OriginalBishopPointwiseComplexConverges
    (Newton.originalBishopNewtonOrbit T nz)
    (originalBishopSelectedNewtonLimit T nz input)
originalBishopSelectedNewtonConverges T nz input =
  Limit.originalBishopGeometricOrbitConverges
    (Newton.originalBishopNewtonOrbit T nz)
    Constants.bishopSelectedNewtonIncrementConstant
    Constants.bishopSelectedNewtonRatio
    (originalSelectedNewtonBoundsBuildBishopConvergenceInputs
      T nz input)

-- The SOURCE endomap limit must be witnessed by an actual continuity
-- proof. From it, the same Newton stream has two limits; uniqueness
-- constructs the fixed-point equation without any Banach postulate.
originalBishopSelectedNewtonLimitIsOperatorFixed :
  ∀ T nz →
  (input : OriginalBishopNewtonSelectedStepBounds T nz) →
  Completion.OriginalBishopPointwiseComplexConverges
    (λ n → Newton.originalBishopNewtonOperator T nz
      (Newton.originalBishopNewtonOrbit T nz n))
    (Newton.originalBishopNewtonOperator T nz
      (originalBishopSelectedNewtonLimit T nz input)) →
  Complex._≈C_
    (Newton.originalBishopNewtonOperator T nz
      (originalBishopSelectedNewtonLimit T nz input))
    (originalBishopSelectedNewtonLimit T nz input)
originalBishopSelectedNewtonLimitIsOperatorFixed T nz input continuity =
  let
    limit = originalBishopSelectedNewtonLimit T nz input
    successor =
      Shift.originalBishopComplexSuccessorConvergesToSame
        (Newton.originalBishopNewtonOrbit T nz)
        limit
        (originalBishopSelectedNewtonConverges T nz input)
  in
  BishopSequence.uniqueness-of-limits
    (Complex.re (Newton.originalBishopNewtonOperator T nz limit) ,
      Completion.realConverges continuity)
    (Complex.re limit , Completion.realConverges successor)
  ,
  BishopSequence.uniqueness-of-limits
    (Complex.im (Newton.originalBishopNewtonOperator T nz limit) ,
      Completion.imaginaryConverges continuity)
    (Complex.im limit , Completion.imaginaryConverges successor)


------------------------------------------------------------------------
-- END-TO-END CONSTRUCTIVE NEWTON CONSUMER.
-- Only the two genuine source analytic leaves remain:
--   original Newton step geometric bounds, operator continuity.
-- All completion and fixed-point-to-exponential cancellation is paid
-- by the actual source lemmas above.
------------------------------------------------------------------------

originalBishopSelectedNewtonLimitIsNativeExpFixed :
  ∀ T nz →
  (input : OriginalBishopNewtonSelectedStepBounds T nz) →
  Completion.OriginalBishopPointwiseComplexConverges
    (λ n → Newton.originalBishopNewtonOperator T nz
      (Newton.originalBishopNewtonOrbit T nz n))
    (Newton.originalBishopNewtonOperator T nz
      (originalBishopSelectedNewtonLimit T nz input)) →
  Complex._≈C_
    (Native.originalBishopExpOnSeries T
      (originalBishopSelectedNewtonLimit T nz input))
    (originalBishopSelectedNewtonLimit T nz input)
originalBishopSelectedNewtonLimitIsNativeExpFixed
  T nz input continuity =
  Newton.originalBishopNewtonOperatorFixedImpliesExpFixed
    T nz
    (originalBishopSelectedNewtonLimit T nz input)
    (originalBishopSelectedNewtonLimitIsOperatorFixed
      T nz input continuity)
