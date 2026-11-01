module DASHI.Analysis.DashiWeightedValuationWeilCandidate where

-- Candidate instantiation of the DASHI quadratic using the repository's
-- concrete weighted p-adic valuation energy.  The adapter is assumption-
-- guarded: exact agreement with the Riemann arithmetic form must be proved.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using (Int)
open import DASHI.Arithmetic.WeightedValuationEnergy using
  (weightedQuadraticEnergy)
open import DASHI.Analysis.RiemannAnalyticSubstrate
open import DASHI.Analysis.RiemannFormulaAnalyticCompatibility
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannExplicitFormula
open import DASHI.Analysis.DashiWeilExactIdentification
open import DASHI.Analysis.WeilConvolutionSquare
open import DASHI.Analysis.RiemannWeilSquareCriterion
open import DASHI.Analysis.DashiWeilSquareBridge

record WeightedValuationWeilBridge
  (space : WeilTestSpace)
  (formula : RiemannExplicitFormula space) : Set₁ where
  open WeilTestSpace space
  open RiemannExplicitFormula formula
  field
    liftNat : Nat → Scalar
    embedInteger : Int → Test

    embeddedIntegerAdmissible :
      (n : Int) →
      admissible (embedInteger n)

    weightedEnergyArithmeticAgreement :
      (n : Int) →
      liftNat (weightedQuadraticEnergy n)
      ≡
      arithmeticForm (embedInteger n)

    weightedEnergyNonnegative :
      (n : Int) →
      nonnegative (liftNat (weightedQuadraticEnergy n))

weightedValuationDashiQuadratic :
  (space : WeilTestSpace) →
  (formula : RiemannExplicitFormula space) →
  WeightedValuationWeilBridge space formula →
  DashiWeilQuadratic space formula
weightedValuationDashiQuadratic space formula bridge = record
  { DashiTest = Int
  ; dashiQuadratic =
      λ n →
        WeightedValuationWeilBridge.liftNat bridge
          (weightedQuadraticEnergy n)
  ; embed = WeightedValuationWeilBridge.embedInteger bridge
  ; embeddedAdmissible =
      WeightedValuationWeilBridge.embeddedIntegerAdmissible bridge
  ; dashiArithmeticAgreement =
      WeightedValuationWeilBridge.weightedEnergyArithmeticAgreement bridge
  ; dashiCoercive =
      WeightedValuationWeilBridge.weightedEnergyNonnegative bridge
  }

record WeightedValuationSquareEncoding
  (space : WeilTestSpace)
  (formula : RiemannExplicitFormula space)
  (algebra : WeilConvolutionAlgebra space)
  (bridge : WeightedValuationWeilBridge space formula) : Set₁ where
  field
    encodeGeneratorAsInteger :
      WeilConvolutionAlgebra.Generator algebra → Int

    encodedIntegerIsSquare :
      (g : WeilConvolutionAlgebra.Generator algebra) →
      WeightedValuationWeilBridge.embedInteger bridge
        (encodeGeneratorAsInteger g)
      ≡
      WeilConvolutionAlgebra.convolutionSquare algebra g

weightedValuationSquareAsDashiEncoding :
  (space : WeilTestSpace) →
  (formula : RiemannExplicitFormula space) →
  (algebra : WeilConvolutionAlgebra space) →
  (bridge : WeightedValuationWeilBridge space formula) →
  WeightedValuationSquareEncoding space formula algebra bridge →
  DashiWeilSquareEncoding
    space formula algebra
    (weightedValuationDashiQuadratic space formula bridge)
weightedValuationSquareAsDashiEncoding
  space formula algebra bridge encoding = record
  { encodeGenerator =
      WeightedValuationSquareEncoding.encodeGeneratorAsInteger encoding
  ; encodedTestIsSquare =
      WeightedValuationSquareEncoding.encodedIntegerIsSquare encoding
  }

record WeightedValuationSquareMillenniumAssembly : Set₁ where
  field
    analytic : AnalyticSubstrate
    space : WeilTestSpace
    formula : RiemannExplicitFormula space
    compatibility :
      RiemannFormulaAnalyticCompatibility analytic space formula
    convolutionAlgebra : WeilConvolutionAlgebra space
    weightedValuationBridge :
      WeightedValuationWeilBridge space formula
    squareEncoding :
      WeightedValuationSquareEncoding
        space formula convolutionAlgebra weightedValuationBridge
    separator :
      WeilSquareOffLineSeparator
        analytic space formula convolutionAlgebra

weightedValuationSquareAssemblyImpliesRH :
  (assembly : WeightedValuationSquareMillenniumAssembly) →
  RiemannHypothesisFor
    (WeightedValuationSquareMillenniumAssembly.analytic assembly)
weightedValuationSquareAssemblyImpliesRH assembly =
  let analytic = WeightedValuationSquareMillenniumAssembly.analytic assembly
      space = WeightedValuationSquareMillenniumAssembly.space assembly
      formula = WeightedValuationSquareMillenniumAssembly.formula assembly
      algebra =
        WeightedValuationSquareMillenniumAssembly.convolutionAlgebra assembly
      bridge =
        WeightedValuationSquareMillenniumAssembly.weightedValuationBridge
          assembly
      encoding =
        WeightedValuationSquareMillenniumAssembly.squareEncoding assembly
      separator =
        WeightedValuationSquareMillenniumAssembly.separator assembly
      dashi = weightedValuationDashiQuadratic space formula bridge
      dashiEncoding =
        weightedValuationSquareAsDashiEncoding
          space formula algebra bridge encoding
      dashiAssembly : DashiWeilSquareMillenniumAssembly
      dashiAssembly = record
        { analytic = analytic
        ; space = space
        ; formula = formula
        ; compatibility =
            WeightedValuationSquareMillenniumAssembly.compatibility assembly
        ; convolutionAlgebra = algebra
        ; dashi = dashi
        ; squareEncoding = dashiEncoding
        ; separator = separator
        }
  in
  dashiWeilSquareAssemblyImpliesRH dashiAssembly
