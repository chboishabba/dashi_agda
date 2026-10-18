module DASHI.Analysis.OrdinaryComplexInverseWitnessIndependenceValidation where

open import DASHI.Core.Prelude

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Analysis.OrdinaryComplexInverseWitnessIndependenceExact as P

realReciprocalRegression :
  ∀ {R : Real.ConstructedOrderedCompleteReal} ->
  (D : Polar.RealDivisionAndSquareRoot R) ->
  (x : Real.Real R) ->
  (nx ny : Polar.Nonzero D x) ->
  Polar.reciprocal D x nx ≡ Polar.reciprocal D x ny
realReciprocalRegression = P.realReciprocalWitnessIndependent

complexInverseRegression :
  ∀ {R : Real.ConstructedOrderedCompleteReal}
    {D : Polar.RealDivisionAndSquareRoot R} ->
  (F : Polar.ComplexFieldAuthority R D) ->
  (z : Complex.ComplexPair R) ->
  (nz₁ nz₂ : Polar.NonzeroC F z) ->
  Polar.inverseC F z nz₁ ≡ Polar.inverseC F z nz₂
complexInverseRegression = P.complexInverseWitnessIndependent
