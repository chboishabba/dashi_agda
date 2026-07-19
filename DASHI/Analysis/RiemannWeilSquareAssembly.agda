module DASHI.Analysis.RiemannWeilSquareAssembly where

-- Sharpest current terminal theorem: exact arithmetic positivity on every Weil
-- convolution square, plus the off-line-zero separator, yields RH for the same
-- completed-zeta substrate.

open import DASHI.Analysis.RiemannAnalyticSubstrate
open import DASHI.Analysis.RiemannFormulaAnalyticCompatibility
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannExplicitFormula
open import DASHI.Analysis.WeilConvolutionSquare
open import DASHI.Analysis.RiemannWeilSquareCriterion
open import DASHI.Analysis.RiemannWeilSquareCoercivity

record WeilSquareMillenniumAssembly : Set₁ where
  field
    analytic : AnalyticSubstrate
    space : WeilTestSpace
    formula : RiemannExplicitFormula space
    compatibility :
      RiemannFormulaAnalyticCompatibility analytic space formula
    convolutionAlgebra : WeilConvolutionAlgebra space
    arithmeticSquareCoercivity :
      ArithmeticSquarePositiveDecomposition
        space formula convolutionAlgebra
    separator :
      WeilSquareOffLineSeparator
        analytic space formula convolutionAlgebra

weilSquareAssemblyImpliesRH :
  (assembly : WeilSquareMillenniumAssembly) →
  RiemannHypothesisFor
    (WeilSquareMillenniumAssembly.analytic assembly)
weilSquareAssemblyImpliesRH assembly =
  let analytic = WeilSquareMillenniumAssembly.analytic assembly
      space = WeilSquareMillenniumAssembly.space assembly
      formula = WeilSquareMillenniumAssembly.formula assembly
      algebra = WeilSquareMillenniumAssembly.convolutionAlgebra assembly
      coercivity =
        WeilSquareMillenniumAssembly.arithmeticSquareCoercivity assembly
      separator = WeilSquareMillenniumAssembly.separator assembly
      squarePositive =
        arithmeticSquareCoercivityImpliesSpectralSquarePositivity
          space formula algebra coercivity
  in
  weilSquarePositivityImpliesRH
    analytic space formula algebra separator squarePositive
