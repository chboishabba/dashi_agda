module DASHI.Moonshine.EisensteinComponentwiseComplexLimitExact where

------------------------------------------------------------------------
-- COMPONENTWISE COMPLEX LIMIT COMPILER FOR E4/E6
--
-- ConcreteComplex is literally a pair of constructed reals.  No separate
-- complex Banach-space axiom is needed merely to propagate sequential limits:
-- real sum/product/difference limit laws compile componentwise to the ordinary
-- complex operations.
--
-- This owner then turns convergence of the four coordinate sequences
--
--   Re E4_N, Im E4_N, Re E6_N, Im E6_N
--
-- into the exact E4E6TruncationConvergence object consumed by the Delta/j
-- finite-to-infinite compiler.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Finite
import DASHI.Moonshine.EisensteinTruncationConvergenceCompilerExact as Limit

private
  RealCarrier :
    (C : Complex.ConstructedComplexPackage) → Set
  RealCarrier C =
    Real.Real (Real.real (Complex.realPackage C))

  ComplexCarrier :
    (C : Complex.ConstructedComplexPackage) → Set
  ComplexCarrier C =
    Complex.ComplexPair (Real.real (Complex.realPackage C))

------------------------------------------------------------------------
-- 1. Minimal real sequential limit algebra.
------------------------------------------------------------------------

record RealSequentialLimitAlgebra
    (C : Complex.ConstructedComplexPackage) : Set₁ where

  private
    R = Real.real (Complex.realPackage C)

  field
    ConvergesTo :
      (Nat → RealCarrier C) →
      RealCarrier C →
      Set

    constantLimit :
      (x : RealCarrier C) →
      ConvergesTo (λ _ → x) x

    sumLimit :
      ∀ {left right x y} →
      ConvergesTo left x →
      ConvergesTo right y →
      ConvergesTo
        (λ n → Real._+_ R (left n) (right n))
        (Real._+_ R x y)

    differenceLimit :
      ∀ {left right x y} →
      ConvergesTo left x →
      ConvergesTo right y →
      ConvergesTo
        (λ n → Real._-_ R (left n) (right n))
        (Real._-_ R x y)

    productLimit :
      ∀ {left right x y} →
      ConvergesTo left x →
      ConvergesTo right y →
      ConvergesTo
        (λ n → Real._*_ R (left n) (right n))
        (Real._*_ R x y)

open RealSequentialLimitAlgebra public

------------------------------------------------------------------------
-- 2. Componentwise complex convergence.
------------------------------------------------------------------------

ComplexConvergesTo :
  ∀ {C} →
  RealSequentialLimitAlgebra C →
  (Nat → ComplexCarrier C) →
  ComplexCarrier C →
  Set
ComplexConvergesTo L sequence value =
  ConvergesTo L
    (λ n → Complex.re (sequence n))
    (Complex.re value)
  ×
  ConvergesTo L
    (λ n → Complex.im (sequence n))
    (Complex.im value)

componentwiseConstant :
  ∀ {C} →
  (L : RealSequentialLimitAlgebra C) →
  (z : ComplexCarrier C) →
  ComplexConvergesTo L (λ _ → z) z
componentwiseConstant L (Complex.complex x y) =
  constantLimit L x , constantLimit L y

componentwiseSum :
  ∀ {C} →
  (L : RealSequentialLimitAlgebra C) →
  ∀ {left right x y} →
  ComplexConvergesTo L left x →
  ComplexConvergesTo L right y →
  ComplexConvergesTo L
    (λ n → Complex._+C_ (left n) (right n))
    (Complex._+C_ x y)
componentwiseSum L leftConv rightConv =
  sumLimit L (proj₁ leftConv) (proj₁ rightConv) ,
  sumLimit L (proj₂ leftConv) (proj₂ rightConv)

componentwiseDifference :
  ∀ {C} →
  (L : RealSequentialLimitAlgebra C) →
  ∀ {left right x y} →
  ComplexConvergesTo L left x →
  ComplexConvergesTo L right y →
  ComplexConvergesTo L
    (λ n → Complex._-C_ (left n) (right n))
    (Complex._-C_ x y)
componentwiseDifference L leftConv rightConv =
  differenceLimit L (proj₁ leftConv) (proj₁ rightConv) ,
  differenceLimit L (proj₂ leftConv) (proj₂ rightConv)

componentwiseProduct :
  ∀ {C} →
  (L : RealSequentialLimitAlgebra C) →
  ∀ {left right x y} →
  ComplexConvergesTo L left x →
  ComplexConvergesTo L right y →
  ComplexConvergesTo L
    (λ n → Complex._*C_ (left n) (right n))
    (Complex._*C_ x y)
componentwiseProduct {C} L leftConv rightConv =
  differenceLimit L
    (productLimit L (proj₁ leftConv) (proj₁ rightConv))
    (productLimit L (proj₂ leftConv) (proj₂ rightConv))
  ,
  sumLimit L
    (productLimit L (proj₁ leftConv) (proj₂ rightConv))
    (productLimit L (proj₂ leftConv) (proj₁ rightConv))

------------------------------------------------------------------------
-- 3. Exact ComplexSequentialLimitAlgebra instance.
------------------------------------------------------------------------

componentwiseComplexLimitAlgebra :
  ∀ {C} →
  RealSequentialLimitAlgebra C →
  Limit.ComplexSequentialLimitAlgebra C
componentwiseComplexLimitAlgebra L =
  record
    { Limit.ConvergesTo = ComplexConvergesTo L
    ; Limit.productLimit = componentwiseProduct L
    ; Limit.differenceLimit = componentwiseDifference L
    ; Limit.constantLimit = componentwiseConstant L
    }

------------------------------------------------------------------------
-- 4. Four real coordinate limits compile to E4/E6 complex convergence.
------------------------------------------------------------------------

record E4E6CoordinateLimits
    (C : Complex.ConstructedComplexPackage)
    (L : RealSequentialLimitAlgebra C)
    (kernel : Finite.DivisorPowerKernel)
    (tau : ComplexCarrier C) : Set₁ where
  constructor e4e6-coordinate-limits
  field
    e4Limit e6Limit : ComplexCarrier C

    e4RealConverges :
      ConvergesTo L
        (λ n →
          Complex.re
            (Finite.e4Truncated C kernel n tau))
        (Complex.re e4Limit)

    e4ImagConverges :
      ConvergesTo L
        (λ n →
          Complex.im
            (Finite.e4Truncated C kernel n tau))
        (Complex.im e4Limit)

    e6RealConverges :
      ConvergesTo L
        (λ n →
          Complex.re
            (Finite.e6Truncated C kernel n tau))
        (Complex.re e6Limit)

    e6ImagConverges :
      ConvergesTo L
        (λ n →
          Complex.im
            (Finite.e6Truncated C kernel n tau))
        (Complex.im e6Limit)

open E4E6CoordinateLimits public

compileCoordinateLimits :
  ∀ {C L kernel tau} →
  E4E6CoordinateLimits C L kernel tau →
  Limit.E4E6TruncationConvergence
    C
    (componentwiseComplexLimitAlgebra L)
    kernel
    tau
compileCoordinateLimits coordinates =
  record
    { Limit.infiniteE4 = e4Limit coordinates
    ; Limit.infiniteE6 = e6Limit coordinates
    ; Limit.e4TruncationsConverge =
        e4RealConverges coordinates ,
        e4ImagConverges coordinates
    ; Limit.e6TruncationsConverge =
        e6RealConverges coordinates ,
        e6ImagConverges coordinates
    }

------------------------------------------------------------------------
-- 5. Frontier.
------------------------------------------------------------------------

record ComponentwiseEisensteinLimitBoundary : Set where
  constructor componentwise-eisenstein-limit-boundary
  field
    complexCarrierLiterallyRealPair : Bool
    realLimitAlgebraCompilesComplexProduct : Bool
    realLimitAlgebraCompilesComplexDifference : Bool
    fourCoordinateLimitsCompileE4E6Convergence : Bool
    coordinateLimitsProvedFromPolynomialGeometricMajorantsHere : Bool

open import Agda.Builtin.Bool using (Bool; true; false)
open ComponentwiseEisensteinLimitBoundary public

canonicalComponentwiseEisensteinLimitBoundary :
  ComponentwiseEisensteinLimitBoundary
canonicalComponentwiseEisensteinLimitBoundary =
  componentwise-eisenstein-limit-boundary
    true true true true false
