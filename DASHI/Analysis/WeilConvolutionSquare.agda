module DASHI.Analysis.WeilConvolutionSquare where

-- Weil's positivity criterion is naturally stated on convolution squares
-- g * g∨.  This module separates the generator space from the explicit-formula
-- test space and requires the square construction to land in the admissible
-- domain.

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Analysis.WeilTestSpace

record WeilConvolutionAlgebra (space : WeilTestSpace) : Set₁ where
  open WeilTestSpace space
  field
    Generator : Set

    reverseConjugate : Generator → Generator
    convolution : Generator → Generator → Test
    convolutionSquare : Generator → Test

    squareDefinition :
      (g : Generator) →
      convolutionSquare g
      ≡ convolution g (reverseConjugate g)

    squareAdmissible :
      (g : Generator) →
      admissible (convolutionSquare g)
