module DASHI.Analysis.DashiWeilSquareBridge where

-- Direct DASHI-to-Weil-square route.  Every convolution-square generator must
-- be encoded by a DASHI test whose existing embedding is exactly that square.
-- DASHI coercivity then transports to all Weil squares without a separate
-- density theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Analysis.RiemannAnalyticSubstrate
open import DASHI.Analysis.RiemannFormulaAnalyticCompatibility
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannExplicitFormula
open import DASHI.Analysis.DashiWeilExactIdentification
open import DASHI.Analysis.WeilConvolutionSquare
open import DASHI.Analysis.RiemannWeilSquareCriterion

congSquare :
  {A B : Set} →
  (f : A → B) →
  {x y : A} →
  x ≡ y →
  f x ≡ f y
congSquare f refl = refl

record DashiWeilSquareEncoding
  (space : WeilTestSpace)
  (formula : RiemannExplicitFormula space)
  (algebra : WeilConvolutionAlgebra space)
  (dashi : DashiWeilQuadratic space formula) : Set₁ where
  field
    encodeGenerator :
      WeilConvolutionAlgebra.Generator algebra →
      DashiWeilQuadratic.DashiTest dashi

    encodedTestIsSquare :
      (g : WeilConvolutionAlgebra.Generator algebra) →
      DashiWeilQuadratic.embed dashi (encodeGenerator g)
      ≡
      WeilConvolutionAlgebra.convolutionSquare algebra g

dashiCoercivityImpliesSquarePositivity :
  (space : WeilTestSpace) →
  (formula : RiemannExplicitFormula space) →
  (algebra : WeilConvolutionAlgebra space) →
  (dashi : DashiWeilQuadratic space formula) →
  DashiWeilSquareEncoding space formula algebra dashi →
  (g : WeilConvolutionAlgebra.Generator algebra) →
  WeilTestSpace.nonnegative space
    (RiemannExplicitFormula.spectralZeroForm formula
      (WeilConvolutionAlgebra.convolutionSquare algebra g))
dashiCoercivityImpliesSquarePositivity
  space formula algebra dashi encoding g =
  WeilTestSpace.nonnegativeTransport space
    (congSquare
      (RiemannExplicitFormula.spectralZeroForm formula)
      (DashiWeilSquareEncoding.encodedTestIsSquare encoding g))
    (embeddedSpectralPositive space formula dashi
      (DashiWeilSquareEncoding.encodeGenerator encoding g))

record DashiWeilSquareMillenniumAssembly : Set₁ where
  field
    analytic : AnalyticSubstrate
    space : WeilTestSpace
    formula : RiemannExplicitFormula space
    compatibility :
      RiemannFormulaAnalyticCompatibility analytic space formula
    convolutionAlgebra : WeilConvolutionAlgebra space
    dashi : DashiWeilQuadratic space formula
    squareEncoding :
      DashiWeilSquareEncoding
        space formula convolutionAlgebra dashi
    separator :
      WeilSquareOffLineSeparator
        analytic space formula convolutionAlgebra

dashiWeilSquareAssemblyImpliesRH :
  (assembly : DashiWeilSquareMillenniumAssembly) →
  RiemannHypothesisFor
    (DashiWeilSquareMillenniumAssembly.analytic assembly)
dashiWeilSquareAssemblyImpliesRH assembly =
  let analytic = DashiWeilSquareMillenniumAssembly.analytic assembly
      space = DashiWeilSquareMillenniumAssembly.space assembly
      formula = DashiWeilSquareMillenniumAssembly.formula assembly
      algebra =
        DashiWeilSquareMillenniumAssembly.convolutionAlgebra assembly
      dashi = DashiWeilSquareMillenniumAssembly.dashi assembly
      encoding =
        DashiWeilSquareMillenniumAssembly.squareEncoding assembly
      separator = DashiWeilSquareMillenniumAssembly.separator assembly
      squarePositive =
        dashiCoercivityImpliesSquarePositivity
          space formula algebra dashi encoding
  in
  weilSquarePositivityImpliesRH
    analytic space formula algebra separator squarePositive
