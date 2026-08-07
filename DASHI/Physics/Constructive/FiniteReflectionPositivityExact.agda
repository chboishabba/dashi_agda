module DASHI.Physics.Constructive.FiniteReflectionPositivityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions I",
-- Communications in Mathematical Physics 31 (1973), 83--112.
-- DOI: 10.1007/BF01645738.
--
-- DASHI CONTRIBUTION
--
-- Construct an exact two-state reflection-positive kernel.  Reflection swaps
-- the two halves, while the measure couples only equal reflected boundary
-- states.  The OS quadratic form of a half-observable F is exactly
--
--   F(+)^2 + F(-)^2.
--
-- Hence reflection positivity is witnessed as a sum of rational squares.
-- This is a finite OS2 model, not reflection positivity of the interacting
-- Yang--Mills lattice measure.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

record HalfObservable : Set where
  constructor halfObservable
  field
    valuePlus valueMinus : ℚ

open HalfObservable public

record ReflectedBoundaryPair : Set where
  constructor reflectedPair
  field
    positiveBoundary negativeBoundary : ℚ

reflection : ReflectedBoundaryPair → ReflectedBoundaryPair
reflection (reflectedPair positive negative) =
  reflectedPair negative positive

reflectionInvolutive : ∀ pair → reflection (reflection pair) ≡ pair
reflectionInvolutive (reflectedPair positive negative) = refl

reflectionQuadratic : HalfObservable → ℚ
reflectionQuadratic observable =
  valuePlus observable * valuePlus observable
  + valueMinus observable * valueMinus observable

record SumOfTwoSquares (value : ℚ) : Set where
  constructor sumOfTwoSquares
  field
    firstSquareRoot secondSquareRoot : ℚ
    squareIdentity :
      value
      ≡ firstSquareRoot * firstSquareRoot
        + secondSquareRoot * secondSquareRoot

open SumOfTwoSquares public

reflectionQuadraticIsSumOfSquares : ∀ observable →
  SumOfTwoSquares (reflectionQuadratic observable)
reflectionQuadraticIsSumOfSquares observable =
  sumOfTwoSquares
    (valuePlus observable)
    (valueMinus observable)
    refl

record DiagonalReflectionKernel : Set where
  constructor diagonalReflectionKernel
  field
    plusWeight minusWeight : ℚ

canonicalKernel : DiagonalReflectionKernel
canonicalKernel = diagonalReflectionKernel 1 1

kernelQuadratic : DiagonalReflectionKernel → HalfObservable → ℚ
kernelQuadratic kernel observable =
  plusWeight kernel * valuePlus observable * valuePlus observable
  + minusWeight kernel * valueMinus observable * valueMinus observable

canonicalKernelAgreesWithReflectionQuadratic : ∀ observable →
  kernelQuadratic canonicalKernel observable
  ≡ reflectionQuadratic observable
canonicalKernelAgreesWithReflectionQuadratic observable =
  solve (valuePlus observable ∷ valueMinus observable ∷ [])

canonicalKernelReflectionPositive : ∀ observable →
  SumOfTwoSquares (kernelQuadratic canonicalKernel observable)
canonicalKernelReflectionPositive observable =
  transport
    (reflectionQuadraticIsSumOfSquares observable)
    (canonicalKernelAgreesWithReflectionQuadratic observable)
  where
    transport : ∀ {left right : ℚ} →
      SumOfTwoSquares right → left ≡ right → SumOfTwoSquares left
    transport certificate refl = certificate

record InteractingOS2Boundary : Set₁ where
  field
    GaugeConfiguration : Set
    reflectionMap : GaugeConfiguration → GaugeConfiguration
    positiveTimeObservable : Set
    euclideanMeasure : Set
    reflectedObservableProduct : Set
    measureIntegrability : Set
    osQuadraticNonnegative : Set
    transferMatrixConstruction : Set
