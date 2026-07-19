module DASHI.Analysis.DashiWeightedValuationSquareCoercivity where

-- More flexible weighted-valuation route: the existing DASHI energy is the
-- coercive core of the arithmetic Weil-square functional, while every missing
-- all-prime, archimedean, pole, and trivial-zero contribution is carried by a
-- separately nonnegative remainder.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using (Int)
open import DASHI.Arithmetic.WeightedValuationEnergy using
  (weightedQuadraticEnergy)
open import DASHI.Analysis.RiemannAnalyticSubstrate
open import DASHI.Analysis.RiemannFormulaAnalyticCompatibility
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannExplicitFormula
open import DASHI.Analysis.WeilConvolutionSquare
open import DASHI.Analysis.RiemannWeilSquareCriterion
open import DASHI.Analysis.RiemannWeilSquareCoercivity
open import DASHI.Analysis.RiemannWeilSquareAssembly

record WeightedValuationSquareCoercivity
  (space : WeilTestSpace)
  (formula : RiemannExplicitFormula space)
  (algebra : WeilConvolutionAlgebra space) : Set₁ where
  open WeilTestSpace space
  open RiemannExplicitFormula formula
  field
    encodeGeneratorAsInteger :
      WeilConvolutionAlgebra.Generator algebra → Int

    liftNat : Nat → Scalar
    correctionRemainder :
      WeilConvolutionAlgebra.Generator algebra → Scalar

    arithmeticSquareDecomposition :
      (g : WeilConvolutionAlgebra.Generator algebra) →
      arithmeticForm
        (WeilConvolutionAlgebra.convolutionSquare algebra g)
      ≡
      (liftNat
        (weightedQuadraticEnergy (encodeGeneratorAsInteger g))
       +S correctionRemainder g)

    weightedCorePositive :
      (g : WeilConvolutionAlgebra.Generator algebra) →
      nonnegative
        (liftNat
          (weightedQuadraticEnergy (encodeGeneratorAsInteger g)))

    correctionRemainderPositive :
      (g : WeilConvolutionAlgebra.Generator algebra) →
      nonnegative (correctionRemainder g)

weightedValuationToArithmeticSquareDecomposition :
  (space : WeilTestSpace) →
  (formula : RiemannExplicitFormula space) →
  (algebra : WeilConvolutionAlgebra space) →
  WeightedValuationSquareCoercivity space formula algebra →
  ArithmeticSquarePositiveDecomposition space formula algebra
weightedValuationToArithmeticSquareDecomposition
  space formula algebra bridge = record
  { coerciveCore =
      λ g →
        WeightedValuationSquareCoercivity.liftNat bridge
          (weightedQuadraticEnergy
            (WeightedValuationSquareCoercivity.encodeGeneratorAsInteger
              bridge g))
  ; nonnegativeRemainder =
      WeightedValuationSquareCoercivity.correctionRemainder bridge
  ; arithmeticSquareDecomposition =
      WeightedValuationSquareCoercivity.arithmeticSquareDecomposition bridge
  ; corePositive =
      WeightedValuationSquareCoercivity.weightedCorePositive bridge
  ; remainderPositive =
      WeightedValuationSquareCoercivity.correctionRemainderPositive bridge
  }

record WeightedValuationCoercivityMillenniumAssembly : Set₁ where
  field
    analytic : AnalyticSubstrate
    space : WeilTestSpace
    formula : RiemannExplicitFormula space
    compatibility :
      RiemannFormulaAnalyticCompatibility analytic space formula
    convolutionAlgebra : WeilConvolutionAlgebra space
    weightedCoercivity :
      WeightedValuationSquareCoercivity
        space formula convolutionAlgebra
    separator :
      WeilSquareOffLineSeparator
        analytic space formula convolutionAlgebra

weightedValuationCoercivityImpliesRH :
  (assembly : WeightedValuationCoercivityMillenniumAssembly) →
  RiemannHypothesisFor
    (WeightedValuationCoercivityMillenniumAssembly.analytic assembly)
weightedValuationCoercivityImpliesRH assembly =
  let analytic =
        WeightedValuationCoercivityMillenniumAssembly.analytic assembly
      space = WeightedValuationCoercivityMillenniumAssembly.space assembly
      formula = WeightedValuationCoercivityMillenniumAssembly.formula assembly
      algebra =
        WeightedValuationCoercivityMillenniumAssembly.convolutionAlgebra
          assembly
      weighted =
        WeightedValuationCoercivityMillenniumAssembly.weightedCoercivity
          assembly
      separator =
        WeightedValuationCoercivityMillenniumAssembly.separator assembly
      squareAssembly : WeilSquareMillenniumAssembly
      squareAssembly = record
        { analytic = analytic
        ; space = space
        ; formula = formula
        ; compatibility =
            WeightedValuationCoercivityMillenniumAssembly.compatibility
              assembly
        ; convolutionAlgebra = algebra
        ; arithmeticSquareCoercivity =
            weightedValuationToArithmeticSquareDecomposition
              space formula algebra weighted
        ; separator = separator
        }
  in
  weilSquareAssemblyImpliesRH squareAssembly
