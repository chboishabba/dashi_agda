module DASHI.Analysis.RiemannSeparatorAssembly where

-- Terminal assemblies using the explicit off-line-zero separator rather than
-- an opaque imported Weil criterion.

open import DASHI.Analysis.RiemannAnalyticSubstrate
open import DASHI.Analysis.RiemannFormulaAnalyticCompatibility
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannExplicitFormula
open import DASHI.Analysis.DashiWeilExactIdentification
open import DASHI.Analysis.WeilPositivityCore
open import DASHI.Analysis.WeilDensityClosure
open import DASHI.Analysis.RiemannArithmeticCoercivity
open import DASHI.Analysis.RiemannWeilSeparatorCriterion
open import DASHI.Analysis.RiemannMillenniumAssembly using (exactAsLike)

record SeparatorDashiAssembly : Set₁ where
  field
    analytic : AnalyticSubstrate
    space : WeilTestSpace
    formula : RiemannExplicitFormula space
    compatibility :
      RiemannFormulaAnalyticCompatibility analytic space formula
    dashi : DashiWeilQuadratic space formula
    density :
      SequentialDashiDensity space formula
        (exactAsLike space formula dashi)
    separator : WeilOffLineSeparator analytic space formula

separatorDashiAssemblyImpliesRH :
  (assembly : SeparatorDashiAssembly) →
  RiemannHypothesisFor (SeparatorDashiAssembly.analytic assembly)
separatorDashiAssemblyImpliesRH assembly =
  let analytic = SeparatorDashiAssembly.analytic assembly
      space = SeparatorDashiAssembly.space assembly
      formula = SeparatorDashiAssembly.formula assembly
      dashi = SeparatorDashiAssembly.dashi assembly
      density = SeparatorDashiAssembly.density assembly
      separator = SeparatorDashiAssembly.separator assembly
      completion =
        sequentialDensityToExtension space formula
          (exactAsLike space formula dashi) density
      embeddedPositive = embeddedSpectralPositive space formula dashi
      universalPositive =
        DensePositivityExtension.extendPositive completion embeddedPositive
  in
  universalWeilPositivityImpliesRH
    analytic space formula separator universalPositive

record SeparatorArithmeticCoercivityAssembly : Set₁ where
  field
    analytic : AnalyticSubstrate
    space : WeilTestSpace
    formula : RiemannExplicitFormula space
    compatibility :
      RiemannFormulaAnalyticCompatibility analytic space formula
    arithmeticCoercivity :
      ArithmeticPositiveDecomposition space formula
    separator : WeilOffLineSeparator analytic space formula

-- Most explicit prize-facing endpoint currently in the repository:
-- arithmetic positive decomposition -> spectral Weil positivity ->
-- off-line-zero separation -> RH for the same completed zeta substrate.
separatorArithmeticCoercivityImpliesRH :
  (assembly : SeparatorArithmeticCoercivityAssembly) →
  RiemannHypothesisFor
    (SeparatorArithmeticCoercivityAssembly.analytic assembly)
separatorArithmeticCoercivityImpliesRH assembly =
  let analytic = SeparatorArithmeticCoercivityAssembly.analytic assembly
      space = SeparatorArithmeticCoercivityAssembly.space assembly
      formula = SeparatorArithmeticCoercivityAssembly.formula assembly
      arithmetic =
        SeparatorArithmeticCoercivityAssembly.arithmeticCoercivity assembly
      separator = SeparatorArithmeticCoercivityAssembly.separator assembly
      universalPositive =
        arithmeticCoercivityImpliesWeilPositivity
          space formula arithmetic
  in
  universalWeilPositivityImpliesRH
    analytic space formula separator universalPositive
