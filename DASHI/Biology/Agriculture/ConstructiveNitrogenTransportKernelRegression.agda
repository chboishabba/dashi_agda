module DASHI.Biology.Agriculture.ConstructiveNitrogenTransportKernelRegression where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConstructiveSeries as Series
import DASHI.Analysis.PolynomialGeometricTailDominationExact as Tail
import DASHI.Analysis.TailModulusCauchyBridgeExact as Bridge
import DASHI.Biology.Agriculture.ConstructiveNitrogenTransportKernelExact as P

mineralisationIsConvolutionRegression :
  ∀ (R : Real.ConstructedOrderedCompleteReal)
    (fixedInput mineralisationKernel : Nat → Real.Real R)
    (time : Nat) →
  P.mineralisedNitrogen R fixedInput mineralisationKernel time
  ≡ Series.convolutionCoefficient R fixedInput mineralisationKernel time
mineralisationIsConvolutionRegression R fixedInput mineralisationKernel time =
  refl

captureIsSecondConvolutionRegression :
  ∀ (R : Real.ConstructedOrderedCompleteReal)
    (fixedInput mineralisationKernel captureKernel : Nat → Real.Real R)
    (time : Nat) →
  P.capturedNitrogen
      R fixedInput mineralisationKernel captureKernel time
  ≡ Series.convolutionCoefficient R
      (P.mineralisedNitrogen R fixedInput mineralisationKernel)
      captureKernel
      time
captureIsSecondConvolutionRegression R fixedInput mineralisationKernel captureKernel time =
  refl

routeTailRegression :
  ∀ {Scalar : Set}
    {K : Tail.OrderedTailKernel Scalar}
    {S : Tail.TailSmallness K} →
  (problem : P.NitrogenRouteTailProblem K S) →
  Tail.TailVanishes K S (P.routeContribution problem)
routeTailRegression = P.routeTailVanishes

routeMajorantAbsoluteConvergenceRegression :
  (problem : P.BishopNitrogenRouteMajorant) →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (P.bishopRouteMajorantTerm problem)
routeMajorantAbsoluteConvergenceRegression =
  P.bishopRouteMajorantAbsolutelyConvergent


routeDominatedPartialSumsCauchyRegression :
  (problem : P.BishopNitrogenRouteDominatedSeries) →
  BishopSequence._isCauchy
    (BishopSequence.SeriesOf
      (P.bishopRouteActualContribution problem))
routeDominatedPartialSumsCauchyRegression =
  P.bishopRouteActualPartialSumsCauchy
