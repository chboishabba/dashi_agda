module DASHI.Analysis.RiemannWeilSquareCoercivity where

-- The exact open theorem in its natural domain: decompose the arithmetic
-- explicit-formula value of every convolution square into nonnegative pieces.
-- The theorem below transports that positivity to the spectral zero side.

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannExplicitFormula
open import DASHI.Analysis.WeilConvolutionSquare

record ArithmeticSquarePositiveDecomposition
  (space : WeilTestSpace)
  (formula : RiemannExplicitFormula space)
  (algebra : WeilConvolutionAlgebra space) : Set₁ where
  open WeilTestSpace space
  open RiemannExplicitFormula formula
  field
    coerciveCore :
      WeilConvolutionAlgebra.Generator algebra → Scalar
    nonnegativeRemainder :
      WeilConvolutionAlgebra.Generator algebra → Scalar

    arithmeticSquareDecomposition :
      (g : WeilConvolutionAlgebra.Generator algebra) →
      arithmeticForm
        (WeilConvolutionAlgebra.convolutionSquare algebra g)
      ≡
      (coerciveCore g +S nonnegativeRemainder g)

    corePositive :
      (g : WeilConvolutionAlgebra.Generator algebra) →
      nonnegative (coerciveCore g)

    remainderPositive :
      (g : WeilConvolutionAlgebra.Generator algebra) →
      nonnegative (nonnegativeRemainder g)

arithmeticSquarePositive :
  (space : WeilTestSpace) →
  (formula : RiemannExplicitFormula space) →
  (algebra : WeilConvolutionAlgebra space) →
  (decomposition :
    ArithmeticSquarePositiveDecomposition space formula algebra) →
  (g : WeilConvolutionAlgebra.Generator algebra) →
  WeilTestSpace.nonnegative space
    (RiemannExplicitFormula.arithmeticForm formula
      (WeilConvolutionAlgebra.convolutionSquare algebra g))
arithmeticSquarePositive space formula algebra decomposition g =
  WeilTestSpace.nonnegativeTransport space
    (≡-sym
      (ArithmeticSquarePositiveDecomposition.arithmeticSquareDecomposition
        decomposition g))
    (WeilTestSpace.nonnegativeAdd space
      (ArithmeticSquarePositiveDecomposition.corePositive decomposition g)
      (ArithmeticSquarePositiveDecomposition.remainderPositive
        decomposition g))

arithmeticSquareCoercivityImpliesSpectralSquarePositivity :
  (space : WeilTestSpace) →
  (formula : RiemannExplicitFormula space) →
  (algebra : WeilConvolutionAlgebra space) →
  ArithmeticSquarePositiveDecomposition space formula algebra →
  (g : WeilConvolutionAlgebra.Generator algebra) →
  WeilTestSpace.nonnegative space
    (RiemannExplicitFormula.spectralZeroForm formula
      (WeilConvolutionAlgebra.convolutionSquare algebra g))
arithmeticSquareCoercivityImpliesSpectralSquarePositivity
  space formula algebra decomposition g =
  WeilTestSpace.nonnegativeTransport space
    (RiemannExplicitFormula.explicitFormula formula
      (WeilConvolutionAlgebra.convolutionSquare algebra g)
      (WeilConvolutionAlgebra.squareAdmissible algebra g))
    (arithmeticSquarePositive space formula algebra decomposition g)
